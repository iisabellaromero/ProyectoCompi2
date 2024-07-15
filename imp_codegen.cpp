#include "imp_codegen.hh"

ImpCodeGen::ImpCodeGen(ImpTypeChecker* a):analysis(a) {

}

void ImpCodeGen::codegen(string label, string instr) {
  if (label !=  nolabel)
    code << label << ": ";
  code << instr << endl;  
}

void ImpCodeGen::codegen(string label, string instr, int arg) {
  if (label !=  nolabel)
    code << label << ": ";
  code << instr << " " << arg << endl;
}

void ImpCodeGen::codegen(string label, string instr, string jmplabel) {
  if (label !=  nolabel)
    code << label << ": ";
  code << instr << " " << jmplabel << endl;
}

string ImpCodeGen::next_label() {
  string l = "L";
  string n = to_string(current_label++);
  l.append(n);
  return l;
}

string ImpCodeGen::get_flabel(string fname) {
  string l = "L";
  l.append(fname);
  return l;
}

void ImpCodeGen::codegen(Program* p, string outfname) {
  nolabel = "";
  current_label = 0;

  p->accept(this);
  ofstream outfile;
  outfile.open(outfname);
  outfile << code.str();
  outfile.close();

  return;
}

// Este codigo esta completo
void ImpCodeGen::visit(Program* p) {
  current_dir = 0;  // usado para generar nuebvas firecciones
  direcciones.add_level();
  process_global = true;
  p->var_decs->accept(this);
  process_global = false;

  mem_globals = current_dir; 
  
  // codegen
  codegen("start","skip");
  codegen(nolabel,"enter",mem_globals);
  codegen(nolabel,"alloc",mem_globals);
  codegen(nolabel,"mark");
  codegen(nolabel,"pusha",get_flabel("main"));
  codegen(nolabel,"call");
  codegen(nolabel,"halt");

  p->fun_decs->accept(this);
  direcciones.remove_level();
  return;  
}

void ImpCodeGen::visit(Body * b) {

  // guardar direccion inicial current_dir
  int restoreDir = current_dir;
  current_dir = 0;
  
  direcciones.add_level();
  
  b->var_decs->accept(this);
  b->slist->accept(this);
  
  direcciones.remove_level();

  // restaurar dir
  current_dir = restoreDir;
  return;
}

void ImpCodeGen::visit(VarDecList* s) {
  list<VarDec*>::iterator it;
  for (it = s->vdlist.begin(); it != s->vdlist.end(); ++it) {
    (*it)->accept(this);
  }  
  return;
}

// Se crea entrada para declaraciones de variables
void ImpCodeGen::visit(VarDec* vd) {
  list<string>::iterator it;
  for (it = vd->vars.begin(); it != vd->vars.end(); ++it){
    current_dir++;
    VarEntry ventry;
    ventry.dir = current_dir;
    ventry.is_global = process_global;
    direcciones.add_var(*it, ventry);
  }
  return;
}

void ImpCodeGen::visit(FunDecList* s) {
  list<FunDec*>::iterator it;
  for (it = s->fdlist.begin(); it != s->fdlist.end(); ++it) {
    (*it)->accept(this);
  }
  return;
}

void ImpCodeGen::visit(FunDec* fd) {
  FEntry fentry = analysis->ftable.lookup(fd->fname);
  current_dir = 0;
  int m = fd->types.size();
  VarEntry ventry;

  // agregar direcciones de argumentos
    list<string>::iterator it = fd->vars.begin();
    for (int i = 0; i < fd->vars.size(); ++i){
        current_dir++;
        ventry.dir = current_dir-(m+3);
        ventry.is_global = false;
        direcciones.add_var(*it, ventry);
        std::advance(it, 1);
    }

  // agregar direccion de return
  // si es void no es necesario
  // esto esta raro... el return no debería ir debajo de los argumentos en terminos de direcciones?
  if (fd->rtype != "void") {
    current_dir++;
    ventry.dir = current_dir;
    ventry.is_global = false;
    direcciones.add_var("return", ventry);
  }


  // generar codigo para fundec
  num_params = m;
  mem_locals = fentry.mem_locals;
  max_stack = fentry.max_stack;
    codegen(get_flabel(fd->fname),"skip");
    codegen(nolabel, "enter", max_stack+mem_locals);
    codegen(nolabel, "alloc", mem_locals);

    fd->body->accept(this);

  return;
}


void ImpCodeGen::visit(StatementList* s) {
  list<Stm*>::iterator it;
  for (it = s->slist.begin(); it != s->slist.end(); ++it) {
    (*it)->accept(this);
  }
  return;
}

void ImpCodeGen::visit(AssignStatement* s) {
  s->rhs->accept(this);
  VarEntry ventry = direcciones.lookup(s->id);
  // generar codigo store/storer
  // Si es global, store. Si es local, storer
  if (ventry.is_global) {
      codegen(nolabel, "store", ventry.dir);
  } else {
      codegen(nolabel, "storer", ventry.dir);
  }

  return;
}

void ImpCodeGen::visit(PrintStatement* s) {
  s->e->accept(this);
  code << "print" << endl;;
  return;
}

void ImpCodeGen::visit(IfStatement* s) {
  string l1 = next_label();
  string l2 = next_label();
  
  s->cond->accept(this);
  codegen(nolabel,"jmpz",l1);
  s->tbody->accept(this);
  codegen(nolabel,"goto",l2);
  codegen(l1,"skip");
  if (s->fbody!=NULL) {
    s->fbody->accept(this);
  }
  codegen(l2,"skip");
 
  return;
}

void ImpCodeGen::visit(WhileStatement* s) {
  string l1 = next_label();
  string l2 = next_label();

  codegen(l1,"skip");
  s->cond->accept(this);
  codegen(nolabel,"jmpz",l2);
  s->body->accept(this);
  codegen(nolabel,"goto",l1);
  codegen(l2,"skip");

  return;
}

void ImpCodeGen::visit(ReturnStatement* s) {
  // agregar codigo
  // generar codigo en la pila para obtener el valor
  if (s->e) {
      s->e->accept(this);
      codegen(nolabel, "storer", -(num_params+3));
  }
  codegen(nolabel,"return", num_params+3);
  return;
}


int ImpCodeGen::visit(BinaryExp* e) {
  e->left->accept(this);
  e->right->accept(this);
  string op = "";
  switch(e->op) {
  case PLUS: op =  "add"; break;
  case MINUS: op = "sub"; break;
  case MULT:  op = "mul"; break;
  case DIV:  op = "div"; break;
  case LT:  op = "lt"; break;
  case LTEQ: op = "le"; break;
  case EQ:  op = "eq"; break;
  default: cout << "binop " << Exp::binopToString(e->op) << " not implemented" << endl;
  }
  codegen(nolabel, op);
  return 0;
}

int ImpCodeGen::visit(NumberExp* e) {
  codegen(nolabel,"push ",e->value);
  return 0;
}

int ImpCodeGen::visit(TrueFalseExp* e) {
  codegen(nolabel,"push",e->value?1:0);
 
  return 0;
}

int ImpCodeGen::visit(IdExp* e) {
  VarEntry ventry = direcciones.lookup(e->id);
  if (ventry.is_global)
    codegen(nolabel,"load",ventry.dir);
  else
    codegen(nolabel,"loadr",ventry.dir);
  return 0;
}

int ImpCodeGen::visit(ParenthExp* ep) {
  ep->e->accept(this);
  return 0;
}

int ImpCodeGen::visit(CondExp* e) {
  string l1 = next_label();
  string l2 = next_label();
 
  e->cond->accept(this);
  codegen(nolabel, "jmpz", l1);
  e->etrue->accept(this);
  codegen(nolabel, "goto", l2);
  codegen(l1,"skip");
  e->efalse->accept(this);
  codegen(l2, "skip");
  return 0;
}

int ImpCodeGen::visit(FCallExp* e) {

  FEntry fentry = analysis->ftable.lookup(e->fname);
  ImpType ftype = fentry.ftype;

  // agregar codigo
  // si tiene valor de retorno, hacer alloc
  if (ftype.types.back() != ImpType::TType::VOID) {
      codegen(nolabel, "alloc", 1);
  }
  list<Exp*>::iterator it = e->args.begin();
  for (int i = 0; i < e->args.size(); i++) {
      (*it)->accept(this);
      std::advance(it, 1);
  }
  codegen(nolabel, "mark");
  codegen(nolabel, "pusha", "L"+fentry.fname);
  codegen(nolabel,"call");
  return 0;
}
