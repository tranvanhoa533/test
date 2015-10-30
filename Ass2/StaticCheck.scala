package bkool.checker

/**
 * @author nhphung
 */

import bkool.parser._
import bkool.utils._
import java.io.{PrintWriter, File}
import org.antlr.v4.runtime.ANTLRFileStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree._
import scala.collection.JavaConverters._

//92 test sua loi unary

case object SelFloatType extends Type
case object NullType extends Type
case class Const(_type:Type) extends Type
case class MethodType(parType: List[Type], retType:Type) extends Type
case class CType(name:String,parent:String,subclass:String,memlist:List[Symbol],curMeth:String) extends Type
case class Symbol(name:String,t:Type)
//case class SymbolTable(var memdecl:List[Symbol], var index:List[Int]){
//  def insert(sym:Symbol){
//    val scope = memdecl.splitAt(index.head)._2
//    lookup(sym,scope) match{
//      case None => memdecl = memdecl :+ sym
//      case Some(a) => Redeclared
//    }
//  }
//  def lookup(sym:Symbol, list:List[Symbol]) = list.find(_ == sym) match{
//    case None => None
//    case Some(a) => Some(a)
//  }
//  def enterScope()
//  {
//    (memdecl.length)::index
//  }
//  def exitScope(){
//   memdecl =  memdecl.splitAt(index.head)._1
//   index   =  index match{
//      case List()=>List()
//      case h::t => t
//    }
//  
//  }
//}

class StaticChecker(ast:AST)extends Utils {
    def check() = {
      val list = Symbol("readInt",MethodType(List(),IntType))  :: List[Symbol]()
      val list1 = Symbol("writeInt",MethodType(List(IntType),VoidType)) :: list
      val list2 = Symbol("writeIntLn",MethodType(List(IntType),VoidType)) :: list1
      val list3 = Symbol("readFloat",MethodType(List(),FloatType)) :: list2
      val list4 = Symbol("writeFloat",MethodType(List(FloatType),VoidType)) :: list3
      val list5 = Symbol("writeFloatLn",MethodType(List(FloatType),VoidType)) :: list4
      val list6 = Symbol("readBool",MethodType(List(),BoolType)) :: list5
      val list7 = Symbol("writeBool",MethodType(List(BoolType),VoidType)) :: list6
      val list8 = Symbol("writeBoolLn",MethodType(List(BoolType),VoidType)) :: list7
      val list9 = Symbol("readStr",MethodType(List(),StringType)) :: list8
      val list10 = Symbol("writeStr",MethodType(List(StringType),VoidType)) :: list9
      val list11 = Symbol("writeStrLn",MethodType(List(StringType),VoidType)) :: list10
      val io = CType("io","","",list11,"")
      val lscl = new ClassList()
      val v = io::lscl.visit(ast, O(List())).asInstanceOf[List[CType]]
      val global = new GlobalEnvironment(v)
      val e = global.visit(ast,null).asInstanceOf[List[CType]]
      
      
      val tc = new TypeChecking(e:+io)
      tc.visit(ast,O(List()))
      
    }
}
case class O(o:Object) extends Context
class BKVisitor extends Visitor{ 
  override def visitProgram(ast: Program, c: Context): Object = null
  override def visitClassDecl(ast: ClassDecl, c: Context): Object = null
  override def visitVarDecl(ast: VarDecl, c: Context): Object = null
  override def visitConstDecl(ast: ConstDecl, c: Context): Object= null 
  override def visitParamDecl(ast: ParamDecl, c: Context): Object= null
  override def visitMethodDecl(ast: MethodDecl, c: Context): Object =null
  override def visitAttributeDecl(ast: AttributeDecl, c: Context): Object =  null
  override def visitInstance(ast: Instance.type, c: Context): Object = null
  override def visitStatic(ast: Static.type, c: Context): Object = null
  override def visitIntType(ast: IntType.type, c: Context): Object  = IntType
  override def visitFloatType(ast: FloatType.type, c: Context): Object = FloatType
  override def visitBoolType(ast: BoolType.type, c: Context): Object = BoolType
  override def visitStringType(ast: StringType.type, c: Context): Object = StringType
  override def visitVoidType(ast: VoidType.type, c: Context): Object = VoidType
  override def visitArrayType(ast: ArrayType, c: Context): Object = null
  override def visitClassType(ast: ClassType, c: Context): Object = ast
  override def visitBinaryOp(ast: BinaryOp, c: Context): Object = null
  override def visitUnaryOp(ast: UnaryOp, c: Context): Object = null
  override def visitNewExpr(ast: NewExpr, c: Context): Object = null
  override def visitCallExpr(ast: CallExpr, c: Context): Object = null
  override def visitId(ast: Id, c: Context): Object = null
  override def visitArrayCell(ast: ArrayCell, c: Context): Object = null
  override def visitFieldAccess(ast: FieldAccess, c: Context): Object = null
  override def visitBlock(ast: Block, c: Context): Object = null
  override def visitAssign(ast: Assign, c: Context): Object = null
  override def visitIf(ast: If, c: Context): Object = null
  override def visitCall(ast: Call, c: Context): Object = null
  override def visitWhile(ast: While, c: Context): Object = null
  override def visitBreak(ast: Break.type, c: Context): Object = null
  override def visitContinue(ast: Continue.type, c: Context): Object = null
  override def visitReturn(ast: Return, c: Context): Object = null
  override def visitIntLiteral(ast: IntLiteral, c: Context): Object = IntType
  override def visitFloatLiteral(ast: FloatLiteral, c: Context): Object =FloatType
  override def visitStringLiteral(ast: StringLiteral, c: Context): Object = StringType
  override def visitBooleanLiteral(ast: BooleanLiteral, c: Context): Object = BoolType
  override def visitNullLiteral(ast: NullLiteral.type, c: Context): Object = null
  override def visitSelfLiteral(ast: SelfLiteral.type, c: Context): Object = null
}
class ClassList extends BKVisitor {
  override def visitProgram(ast: Program, c: Context) = ast.decl.foldLeft(List[CType]())((x,y)=> visit(y,O(x)).asInstanceOf[List[CType]])
  override def visitClassDecl(ast: ClassDecl, c: Context) = { 
    val a = c.asInstanceOf[O]
    val e = a.o.asInstanceOf[List[CType]]
    val pr = ast.parent.toString()
    val clname = ast.name.toString() 
    if(e.exists(x=>x.name==clname) || clname=="io") throw Redeclared(Class,clname) else CType(clname,pr,"",List[Symbol](),"") ::e 
  }
}
class GlobalEnvironment(lstCls: List[CType]) extends BKVisitor with Utils{
  override def visitProgram(ast: Program, c: Context) = ast.decl.foldLeft(List[CType]())((x,y)=> visit(y,O(x)).asInstanceOf[List[CType]])
  override def visitClassDecl(ast: ClassDecl, c: Context) = { 
    
    val a = c.asInstanceOf[O]
    val e = a.o.asInstanceOf[List[CType]]
    val pr = ast.parent.toString()
    val clname = ast.name.toString() 
     if (pr!="" && lookupClass(pr,lstCls)==None) throw Undeclared(Class,pr)
    if(e.exists(x=>x.name==clname) || clname=="io") throw Redeclared(Class,clname) else{       
      val classenv = ast.decl.foldLeft(List[Symbol]())((x,y)=> visit(y,O(x)).asInstanceOf[List[Symbol]])
 //    val classenv = ast.decl.foldLeft(CType(ast.name.toString(),ast.parent.toString(),List[Symbol]()))((x,y)=> visit(y,O(x)).asInstanceOf[CType])  
    CType(clname,pr,"",classenv,"") ::e 
    }
  }
  override def visitVarDecl(ast: VarDecl, c: Context)= {
   val a = c.asInstanceOf[O]
 //   val env = a.o.asInstanceOf[CType].memlist
    val env = a.o.asInstanceOf[List[Symbol]]
    val t = visit(ast.varType,O(env)).asInstanceOf[Type]
    if(env.exists(x=>x.name == ast.variable.toString())) throw Redeclared(Attribute, ast.variable.toString()) 
    else{
      if(ast.varType.isInstanceOf[ClassType]){
        val cls = ast.varType.asInstanceOf[ClassType].classType
        if(lookupClass(cls,lstCls)==None) throw Undeclared(Class,cls)
      }
    } 
    Symbol(ast.variable.toString(),ast.varType)::env
  }
  override def visitConstDecl(ast: ConstDecl, c: Context) ={
    val a = c.asInstanceOf[O]
  //  val env = a.o.asInstanceOf[CType].memlist
    val env = a.o.asInstanceOf[List[Symbol]]
    visit(ast.const,c)
    val tconst = visit(ast.constType,O(env)).asInstanceOf[Type]
    if(env.exists(x=>x.name == ast.id.toString())) throw Redeclared(Attribute, ast.id.toString()) 
    else{
      if(ast.constType.isInstanceOf[ClassType]){
        val cls = ast.constType.asInstanceOf[ClassType].classType
        if(lookupClass(cls,lstCls)==None) throw Undeclared(Class,cls)
      }
    }
    val texp = visit(ast.const,c).asInstanceOf[Type]
   
    val tcst = if(tconst.isInstanceOf[ClassType])  tconst.asInstanceOf[ClassType].classType
    texp match{
      case CType(n,p,s,m,cm) => if(n!= tcst) throw TypeMismatchInConstant(ast)
      case Const(tp) => if(!typeCheck(tconst,tp)) throw TypeMismatchInConstant(ast)
      case _ => if(!typeCheck(tconst,texp) )throw TypeMismatchInConstant(ast)
    }
   Symbol(ast.id.toString(),Const(ast.constType))::env
  }
//  override def visitArrayType(ast: ArrayType, c: Context)={
//    val t = visit(ast.eleType,c).asInstanceOf[Type]
//    ArrayType(ast.dimen,t)
//  }
//  override def visitClasStringType(ast: ClasStringType, c: Context)={
//    lookupClass(ast.clasStringType.toString(),lstCls) match{
//      case None => throw Undeclared(Class,ast.clasStringType.toString())
//      case Some(cl) => cl
//    }
//  }
  override def visitMethodDecl(ast: MethodDecl, c: Context)={
    val a = c.asInstanceOf[O]
  //  val e = a.o.asInstanceOf[CType].memlist
    val e = a.o.asInstanceOf[List[Symbol]]
    val rtype=ast.returnType
    if (rtype.isInstanceOf[ClassType]) {
      val cls=rtype.asInstanceOf[ClassType].classType
      if (lookupClass(cls,lstCls)==None) throw Undeclared(Class,cls) 
    }
    val pa = ast.param.foldLeft(List[Symbol]())((x,y)=>(visit(y,O(x)).asInstanceOf[List[Symbol]]))
    val t = MethodType(pa.map(_.t) ,rtype)
    if(e.exists(x=>x.name == ast.name.toString())) throw Redeclared(Method, ast.name.toString()) else Symbol(ast.name.toString(),t)::e
  }
  override def visitParamDecl(ast: ParamDecl, c: Context) = {
    val env = c.asInstanceOf[O].o.asInstanceOf[List[Symbol]]
 //   val env = c.asInstanceOf[O].o.asInstanceOf[CType].memlist
    val name = ast.id.toString
    val ptype=ast.paramType
    if (ptype.isInstanceOf[ClassType]) {
      val cls=ptype.asInstanceOf[ClassType].classType
      if (lookupClass(cls,lstCls)==None) throw Undeclared(Class,cls) 
    }
      
    if (env.exists(_.name==name)) throw Redeclared(Parameter,name) else env:+Symbol(ast.id.toString(),ptype)   
  } 
  override def visitBinaryOp(ast: BinaryOp, c: Context)={
    
    val ltype = visit(ast.left,c).asInstanceOf[Type]
    val rtype = visit(ast.right,c).asInstanceOf[Type]
    ast.op match{ 
      case "^" => if( ltype == StringType && rtype == StringType) StringType else throw TypeMismatchInExpression(ast)
      case ("%" | "\\") => if( ltype == IntType && rtype == IntType) IntType else throw TypeMismatchInExpression(ast)
      case("+" | "-" | "*" ) => if((ltype!=IntType && ltype != FloatType)|| (rtype!=IntType&&rtype!=FloatType)) throw TypeMismatchInExpression(ast) else{
        if(ltype==rtype) ltype else FloatType
      }
      case("/" ) => if((ltype!=IntType && ltype != FloatType) || (rtype!=IntType&&rtype!=FloatType)) throw TypeMismatchInExpression(ast) else{
       FloatType
      }
      case("||" | "&&")=> if(ltype ==BoolType && rtype == BoolType) BoolType else throw TypeMismatchInExpression(ast)
      case ("==" | "<>") => if(ltype != VoidType && rtype != VoidType && ltype==rtype) BoolType else throw TypeMismatchInExpression(ast)
      case (">" | ">=" | "<" | "<=") => if((ltype!=IntType && ltype != FloatType)|| (rtype!=IntType&&rtype!=FloatType)) throw TypeMismatchInExpression(ast) else{
       BoolType
      }
    }
   
 //   c.asInstanceOf[O].o
  }
  override def visitUnaryOp(ast: UnaryOp, c: Context)={
   val t = visit(ast.body,c).asInstanceOf[Type]
    ast.op match{
      case ("+" | "-") => if(t == IntType || t == FloatType) t else throw TypeMismatchInExpression(ast)
      case "!" => if(t==BoolType) BoolType else throw TypeMismatchInExpression(ast)
    }
 //   c.asInstanceOf[O].o
  }
  override def visitAttributeDecl(ast: AttributeDecl, c: Context): Object = {
     visit(ast.decl,c).asInstanceOf[List[Symbol]]
//    val e = c.asInstanceOf[O].o.asInstanceOf[CType]
//    CType(e.name,e.parent,e.memlist++decl)
  }
   override def visitId(ast: Id, c: Context)={
    val local = c.asInstanceOf[O].o.asInstanceOf[List[Symbol]]
   
    local.find { _.name==ast.name } match{
      case None => {
        lstCls.find { _.name==ast.name } match{
          case None => throw Undeclared(Identifier,ast.name)
          case Some(sym) => sym
          }
        }
      case Some(sym) => sym.t
    }
  }
   override def visitFieldAccess(ast: FieldAccess, c: Context)={
    val local = c.asInstanceOf[O].o.asInstanceOf[CType]
    if(ast.name.toString() == SelfLiteral.toString()) 
     { 
      lookupField(local.name,ast.field.toString(),lstCls) match{
      case None => //c.asInstanceOf[O].o
      throw TypeMismatchInExpression(ast) 
      case Some(sym) => sym.t}
    }
    else
     
      visit(ast.name,c).asInstanceOf[Type] match{
      case CType(n,pa,sub,list,m)=>{
        lookupField(n,ast.field.toString(),lstCls) match{
          case None => //c.asInstanceOf[O].o
            throw TypeMismatchInExpression(ast) 
          case Some(sym) => sym.t
        }
      }
      case ClassType(n)=>{
        
        lookupField(n,ast.field.toString(),lstCls) match{
          case None => //c.asInstanceOf[O].o
            throw TypeMismatchInExpression(ast) 
          case Some(sym) => sym.t
        }
      }
      case _ =>// c.asInstanceOf[O].o
        throw TypeMismatchInExpression(ast)
    }
  }
    override def visitArrayCell(ast: ArrayCell, c: Context)={
    
    

    val local = c.asInstanceOf[O].o.asInstanceOf[CType]
    val a = visit(ast.arr,O(local)).asInstanceOf[Type]
    a match{
      case ArrayType(i,e) =>{
         val et = ast.idx.accept(this,O(local)).asInstanceOf[Type]
         if(et == IntType) e else throw TypeMismatchInExpression(ast)
        //e
      }
      case _ => //c.asInstanceOf[O].o//throw Undeclared(Identifier, ast.arr.toString())
        throw  TypeMismatchInExpression(ast)
    }
  }
    override def visitCallExpr(ast: CallExpr, c: Context)={
    val e = c.asInstanceOf[O].o.asInstanceOf[CType]
    val at = ast.params.map(_.accept(this, c)).asInstanceOf[List[Type]]

    if(ast.cName == null)
    { 
      lookupMethod(e.name,ast.method.toString(),at,lstCls,1) match{
      case None => // c.asInstanceOf[O].o
        throw Undeclared(Method,ast.method.toString())/*TypeMismatchInExpression(ast)}*/
      case Some(t) =>// t
        if(t == VoidType) throw TypeMismatchInExpression(ast) else t
    }
    }
    else if(ast.cName.toString() == SelfLiteral.toString()) 
       lookupMethod(e.name,ast.method.toString(),at,lstCls,1) match{
      case None => //c.asInstanceOf[O].o
        throw Undeclared(Method,ast.method.toString())/*TypeMismatchInExpression(ast)*/
      case Some(t) =>// t
        if(t == VoidType) throw TypeMismatchInExpression(ast) else t
    }
    else 
    {
      
       visit(ast.cName,c).asInstanceOf[Type] match{
          case CType(name,pa,sub,lst,m)=> {
            
            lookupMethod(name,ast.method.toString(),at,lstCls,1) match{
              case None => //c.asInstanceOf[O].o
                throw Undeclared(Method,ast.method.toString())/*TypeMismatchInExpression(ast)*/
              case Some(t) =>// t
                if(t == VoidType) throw TypeMismatchInExpression(ast) else t
            }}
          case ClassType(n) =>{
          
            lookupMethod(n,ast.method.toString(),at,lstCls,1) match{
              case None => //c.asInstanceOf[O].o
               
                throw Undeclared(Method,ast.method.toString())/*TypeMismatchInExpression(ast)*/
              case Some(t) =>// t
                if(t == VoidType) throw TypeMismatchInExpression(ast) else t
            }
          }
          case _ =>//c.asInstanceOf[O].o 
            throw  Undeclared(Method,ast.method.toString())/*TypeMismatchInExpression(ast)*/
        }
   }
  } 
    override def visitNewExpr(ast: NewExpr, c: Context)={
 //   val local = c.asInstanceOf[O].o.asInstanceOf[CType].memlist
    val parType = ast.exprs.map(_.accept(this, c)).asInstanceOf[List[Type]]
    lookupNew(ast.name.toString(),ast.name.toString(),ast.name.toString(),ast.name.toString(),parType,lstCls)match{
      case None => throw TypeMismatchInExpression(ast)
      case Some(t) => t
    }
  }
}
class TypeChecking(global:List[CType]) extends BKVisitor with Utils {
  override def visitProgram(ast: Program, c: Context) = ast.decl.foldLeft(List[CType]())((x,y)=> visit(y,O(x)).asInstanceOf[List[CType]])
  override def visitClassDecl(ast: ClassDecl, c: Context) ={
    
    val memlist = insertMemList(ast.name.toString(),global,List[String]()).asInstanceOf[List[Symbol]]
    val cty = CType(ast.name.toString(), ast.parent.toString(),"",memlist,"")
    val _try = CType(ast.name.toString(), ast.parent.toString(),"",List[Symbol](),"")
    ast.decl.filter(_.isInstanceOf[MethodDecl]).map(visit(_,O(_try)))
  } 
  override def visitParamDecl(ast: ParamDecl, c: Context) ={
    val a = c.asInstanceOf[O].o.asInstanceOf[CType]
    val e = a.memlist
//    val t = visit(ast.paramType,O(e)).asInstanceOf[Type]
//    if(e.exists(x=>x.name==ast.id.toString())) throw Redeclared(Parameter,ast.id.toString()) 
//    else {
//      if(t.isInstanceOf[ClassType]){
//        val cls = ast.paramType.asInstanceOf[ClassType].classType
//        if(lookupClass(cls,global)==None) throw Undeclared(Class,cls)
//      }
//    } 7
      CType(a.name,a.parent,"",e:+Symbol(ast.id.toString(),ast.paramType),a.curMeth)
  }
  
  override def visitMethodDecl(ast: MethodDecl, c: Context)={
    val e = c.asInstanceOf[O].o.asInstanceOf[CType]
    val local = ast.param.foldLeft(CType(e.name,e.parent,"",List[Symbol](),e.curMeth))((x,y)=> visit(y,O(x)).asInstanceOf[CType])
    val block = visitBlockMethodDecl(ast.body.asInstanceOf[Block],O(local))
    val all = CType(e.name,e.parent,"",block.memlist ++ e.memlist,ast.name.toString())
    visitBlockMethodStmt(ast.body.asInstanceOf[Block],O(all))
  }
   override def visitVarDecl(ast: VarDecl, c: Context)={
     val a = c.asInstanceOf[O].o.asInstanceOf[CType]
     val e = a.memlist
//     val t = visit(ast.varType,O(e)).asInstanceOf[Type]
    
     if(e.exists(x=>x.name==ast.variable.toString())) throw Redeclared(Variable,ast.variable.toString()) 
     else {
      if(ast.varType.isInstanceOf[ClassType]){
        val cls = ast.varType.asInstanceOf[ClassType].classType
        if(lookupClass(cls,global)==None) throw Undeclared(Class,cls)
      }
    } 
       CType(a.name,a.parent,"",Symbol(ast.variable.toString(),ast.varType):: e,a.curMeth)
   }
  override def visitConstDecl(ast: ConstDecl, c: Context)={
    val a = c.asInstanceOf[O].o.asInstanceOf[CType]
    val e = a.memlist
    
    
    val tconst = visit(ast.constType,O(e)).asInstanceOf[Type]
     if(e.exists(x=>x.name==ast.id.toString())) throw Redeclared(Constant,ast.id.toString()) 
     else {
      if(ast.constType.isInstanceOf[ClassType]){
        val cls = ast.constType.asInstanceOf[ClassType].classType
        if(lookupClass(cls,global)==None) throw Undeclared(Class,cls)
      }
    } 
    val texp = visit(ast.const,c).asInstanceOf[Type]
    texp match{
      case Const(tp) => if(!typeCheck(tconst,tp)) throw TypeMismatchInConstant(ast)
      case _ => if(!typeCheck(tconst,texp) )throw TypeMismatchInConstant(ast)
    }
       CType(a.name,a.parent,"",Symbol(ast.id.toString(),Const(ast.constType)):: e,a.curMeth)
    
  }
  override def visitArrayType(ast: ArrayType, c: Context)={
    val t = visit(ast.eleType,c).asInstanceOf[Type]
    val x = t match{
      case ClassType(t) => lookupClass(t,global) match{
        case None => throw Undeclared(Class,t)
        case Some(t)=> t
      }
    }
    ArrayType(ast.dimen,x)
  }
//  override def visitClassType(ast: ClassType, c: Context)={
//    
//    lookupClass(ast.classType.toString(),global) match{
//      case None => throw Undeclared(Class,ast.classType.toString())
//      case Some(cl) => cl
//    }
//    
//  }
  override def visitBinaryOp(ast: BinaryOp, c: Context)={
    
    val ltype = visit(ast.left,c).asInstanceOf[Type]
    val rtype = visit(ast.right,c).asInstanceOf[Type]
    ast.op match{ 
      case "^" => if( ltype == StringType && rtype == StringType) StringType else throw TypeMismatchInExpression(ast)
      case ("%" | "\\") => if( ltype == IntType && rtype == IntType) IntType else throw TypeMismatchInExpression(ast)
      case("+" | "-" | "*" ) => if((ltype!=IntType && ltype != FloatType)|| (rtype!=IntType&&rtype!=FloatType)) throw TypeMismatchInExpression(ast) else{
        if(ltype==rtype) ltype else FloatType
      }
      case("/" ) => if((ltype!=IntType && ltype != FloatType)|| (rtype!=IntType&&rtype!=FloatType)) throw TypeMismatchInExpression(ast) else{
       FloatType
      }
      case("||" | "&&")=> if(ltype ==BoolType && rtype == BoolType) BoolType else throw TypeMismatchInExpression(ast)
      case ("==" | "<>") => if(ltype != VoidType && rtype != VoidType && ltype==rtype) BoolType else throw TypeMismatchInExpression(ast)
      case (">" | ">=" | "<" | "<=") => if((ltype!=IntType && ltype != FloatType)|| (rtype!=IntType&&rtype!=FloatType)) throw TypeMismatchInExpression(ast) else{
       BoolType
      }
    }
 //   c.asInstanceOf[O].o
  }
  override def visitUnaryOp(ast: UnaryOp, c: Context)={
   val t = visit(ast.body,c).asInstanceOf[Type]
    ast.op match{
      case ("+" | "-") => if(t == IntType || t == FloatType) t else throw TypeMismatchInExpression(ast)
      case "!" => if(t==BoolType) BoolType else throw TypeMismatchInExpression(ast)
    }
   // c.asInstanceOf[O].o
  }
  override def visitNewExpr(ast: NewExpr, c: Context)={
    val local = c.asInstanceOf[O].o.asInstanceOf[CType].memlist
    val parType = ast.exprs.map(_.accept(this, c)).asInstanceOf[List[Type]]
    lookupNew(ast.name.toString(),ast.name.toString(),ast.name.toString(),ast.name.toString(),parType,global)match{
      case None => throw TypeMismatchInExpression(ast)
      case Some(t) => t
    }
  }
  override def visitCallExpr(ast: CallExpr, c: Context)={
    val e = c.asInstanceOf[O].o.asInstanceOf[CType]
    val at = ast.params.map(_.accept(this, c)).asInstanceOf[List[Type]]

    if(ast.cName == null)
    { 
      lookupMethod(e.name,ast.method.toString(),at,global,1) match{
      case None => // c.asInstanceOf[O].o
        //throw Undeclared(Method,ast.method.toString())
        throw TypeMismatchInExpression(ast)
      case Some(t) =>// t
        if(t == VoidType) throw TypeMismatchInExpression(ast) else t
    }
    }
    else if(ast.cName.toString() == SelfLiteral.toString()) 
       lookupMethod(e.name,ast.method.toString(),at,global,1) match{
      case None => //c.asInstanceOf[O].o
       // throw Undeclared(Method,ast.method.toString())
        throw TypeMismatchInExpression(ast)
      case Some(t) =>// t
        if(t == VoidType) throw TypeMismatchInExpression(ast) else t
    }
    else 
    {
      
       visit(ast.cName,c).asInstanceOf[Type] match{
          case CType(name,pa,sub,lst,m)=> {
            
            lookupMethod(name,ast.method.toString(),at,global,1) match{
              case None => //c.asInstanceOf[O].o
                //throw Undeclared(Method,ast.method.toString())
                 throw TypeMismatchInExpression(ast)
              case Some(t) =>// t
                if(t == VoidType) throw TypeMismatchInExpression(ast) else t
            }}
          case ClassType(n) =>{
          
            lookupMethod(n,ast.method.toString(),at,global,1) match{
              case None => //c.asInstanceOf[O].o
               
              //  throw Undeclared(Method,ast.method.toString())
                throw TypeMismatchInExpression(ast)
              case Some(t) =>// t
                if(t == VoidType) throw TypeMismatchInExpression(ast) else t
            }
          }
          case _ =>//c.asInstanceOf[O].o 
           // throw  Undeclared(Method,ast.method.toString())
           throw  TypeMismatchInExpression(ast)
        }
   }
  } 
  override def visitId(ast: Id, c: Context)={
    val local = c.asInstanceOf[O].o.asInstanceOf[CType].memlist
    local.find { _.name==ast.name } match{
      case None => {
        global.find { _.name==ast.name } match{
          case None => throw {
            Undeclared(Identifier,ast.name)}
          case Some(sym) => sym
          }
        }
      case Some(sym) => sym.t
    }
  }
  override def visitArrayCell(ast: ArrayCell, c: Context)={
    
    

    val local = c.asInstanceOf[O].o.asInstanceOf[CType]
    val a = visit(ast.arr,O(local)).asInstanceOf[Type]
    a match{
      case ArrayType(i,e) =>{
         val et = ast.idx.accept(this,O(local)).asInstanceOf[Type]
         if(et == IntType) e else throw TypeMismatchInExpression(ast)
        //e
      }
      case _ => //c.asInstanceOf[O].o//throw Undeclared(Identifier, ast.arr.toString())
        throw  TypeMismatchInExpression(ast)
    }
  }
  override def visitFieldAccess(ast: FieldAccess, c: Context)={
    val local = c.asInstanceOf[O].o.asInstanceOf[CType]
    if(ast.name.toString() == SelfLiteral.toString()) 
     { 
      lookupField(local.name,ast.field.toString(),global) match{
      case None => //c.asInstanceOf[O].o
      throw TypeMismatchInExpression(ast) 
      case Some(sym) => sym.t}
    }
    else
     
      visit(ast.name,c).asInstanceOf[Type] match{
      case CType(n,pa,sub,list,m)=>{
        lookupField(n,ast.field.toString(),global) match{
          case None => //c.asInstanceOf[O].o
            throw TypeMismatchInExpression(ast) 
          case Some(sym) => sym.t
        }
      }
      case ClassType(n)=>{
        
        lookupField(n,ast.field.toString(),global) match{
          case None => //c.asInstanceOf[O].o
            throw TypeMismatchInExpression(ast) 
          case Some(sym) => sym.t
        }
      }
      case _ =>// c.asInstanceOf[O].o
        throw TypeMismatchInExpression(ast)
    }
  }
  override def visitBlock(ast: Block, c: Context)={
   
    val local = c.asInstanceOf[O].o.asInstanceOf[CType]
    val block = ast.decl.foldLeft(CType(local.name,local.parent,"",List[Symbol](),local.curMeth))((x,y)=> visit(y,O(x)).asInstanceOf[CType])
    val all = CType(local.name,local.parent,"",block.memlist ++ local.memlist,local.curMeth)
    ast.stmt.map(_.accept(this, O(all)))
    c.asInstanceOf[O].o
  }
  def visitBlockMethodDecl(ast: Block, c: Context)={
   
    val local = c.asInstanceOf[O].o.asInstanceOf[CType]
    val block = ast.decl.foldLeft(local)((x,y)=> visit(y,O(x)).asInstanceOf[CType])
    CType(local.name,local.parent,"",block.memlist ++ local.memlist,local.curMeth)
    
   
  }
  def visitBlockMethodStmt(ast: Block, c: Context)={
     ast.stmt.map(_.accept(this, c))
  }
  override def visitAssign(ast: Assign, c: Context)={
    val local = c.asInstanceOf[O].o.asInstanceOf[CType]
    val lhsType = visit(ast.leftHandSide,O(local)).asInstanceOf[Type]
    val exptype = visit(ast.expr,O(local)).asInstanceOf[Type]
    if(lhsType == VoidType || exptype == VoidType) throw TypeMismatchInStatement(ast)
//    val l = lhsType match {
//      case ArrayType(d,e) => d
//      case _ => lhsType
//    }
//    val r = exptype match {
//      case ArrayType(d,e) => d
//      case _ => exptype
//    }
    if(lhsType.isInstanceOf[ArrayType]){
      val ldimen = lhsType.asInstanceOf[ArrayType].dimen
      if(exptype.isInstanceOf[ArrayType]){
        val rdimen = exptype.asInstanceOf[ArrayType].dimen
        if(ldimen != rdimen)throw TypeMismatchInStatement(ast)
      }
      else throw TypeMismatchInStatement(ast)
    }
    if(lhsType.isInstanceOf[ClassType]){
      val cl1 = lhsType.asInstanceOf[ClassType].classType
      if(exptype.isInstanceOf[CType]){
        val cl2 = exptype.asInstanceOf[CType].name
        if(!(cl1 == cl2 || findSubClass(cl1,cl2,global)))
          throw TypeMismatchInStatement(ast)
      }
      else if(exptype.isInstanceOf[ClassType]){
        val cl2 = exptype.asInstanceOf[ClassType].classType
        if(!(cl1 == cl2 || findSubClass(cl1,cl2,global)))
          throw TypeMismatchInStatement(ast)
      }
    }
 //   if(l!=r && (l != FloatType && r!=IntType)) throw TypeMismatchInStatement(ast)
   
    val lt = lhsType match{
      case ArrayType(d,e) => e
      case Const(_) => throw CannotAssignToConstant(ast)
      case _ => lhsType
    }
    val rt = exptype match{
      case ArrayType(d,e) => e
      case _ => exptype
    }
   
    if((typeCheck(lt,rt) || (lt==FloatType && rt==IntType))|| !lt.isInstanceOf[ClassType] || !lt.isInstanceOf[CType]) c else throw TypeMismatchInStatement(ast)
    c.asInstanceOf[O].o
  }
  override def visitIf(ast: If, c: Context)={
   val local = c.asInstanceOf[O].o.asInstanceOf[CType]
    val exprtype = visit(ast.expr,O(local)).asInstanceOf[Type]
    val ctype = exprtype match{
     case Const(_type) => _type
     case ArrayType(d,t)=>t
     case _ => exprtype
   }
    if(ctype == BoolType){
      ast.elseStmt match{ 
        case Some(st) =>visit(st.asInstanceOf[Stmt],O(local)) 
        case _ => c
      }
    }
    else throw TypeMismatchInStatement(ast)
   visit(ast.thenStmt,O(local))
 //   val local = c.asInstanceOf[O].o.asInstanceOf[CType]
//    visit(ast.thenStmt,O(local))
//     if (ast.elseStmt!=None) visit(ast.elseStmt.get,O(local))
     ast.elseStmt match{ 
        case Some(st) =>visit(st.asInstanceOf[Stmt],O(local)) 
        case _ => c.asInstanceOf[O].o
      }
     c.asInstanceOf[O].o
  }
  override def visitCall(ast: Call, c: Context)={
    val e = c.asInstanceOf[O].o.asInstanceOf[CType]
    val at = ast.params.map(_.accept(this, c)).asInstanceOf[List[Type]]
    
    if(ast.parent == null)
      {
      lookupMethod(e.name,ast.method.toString(),at,global,2) match{
      case None=> //c.asInstanceOf[O].o 
       // throw Undeclared(Method,ast.method.toString())
        throw TypeMismatchInStatement(ast)
      case Some(t)=>//t
        if(t != VoidType) throw TypeMismatchInStatement(ast) else t
    }}
    else if(ast.parent.toString() == SelfLiteral.toString())
     { 
      
      lookupMethod(e.name,ast.method.toString(),at,global,2) match{
      case None=> //c.asInstanceOf[O].o
        //throw Undeclared(Method,ast.method.toString())
        throw TypeMismatchInStatement(ast)
      case Some(t)=>//t
         if(t != VoidType) throw TypeMismatchInStatement(ast) else t
    }}
    else 
    {
      
      visit(ast.parent,c).asInstanceOf[Type] match {
        case CType(n,p,s,l,m) => lookupMethod(ast.parent.toString(),ast.method.toString(),at,global,2) match{
            case None=> //c.asInstanceOf[O].o
              //throw Undeclared(Method,ast.method.toString())
              throw TypeMismatchInStatement(ast)
            case Some(t)=> //t
               if(t != VoidType) throw TypeMismatchInStatement(ast) else t
      }
        case ClassType(n) =>{
          
          lookupMethod(n,ast.method.toString(),at,global,2) match{
            case None=> //c.asInstanceOf[O].o
              //throw Undeclared(Method,ast.method.toString())
              throw TypeMismatchInStatement(ast)
            case Some(t)=> //t
               if(t != VoidType) throw TypeMismatchInStatement(ast) else t
          }
        }
        case _ => throw TypeMismatchInStatement(ast)
      }
    }
  }
  override def visitWhile(ast: While, c: Context)={
    val local = c.asInstanceOf[O].o.asInstanceOf[CType]
    val exprtype = visit(ast.expr,O(local)).asInstanceOf[Type]
    val ctype = exprtype match{
     case Const(_type) => _type
     case ArrayType(d,t)=>t
     case _ => exprtype
   }
    if(ctype == BoolType){
      visit(ast.loop,O(local))
    }
    else throw TypeMismatchInStatement(ast)
 //   visit(ast.loop,O(local))
    c.asInstanceOf[O].o
  }
  override def visitBreak(ast: Break.type, c: Context): Object = null
  override def visitContinue(ast: Continue.type, c: Context): Object = null
  override def visitReturn(ast: Return, c: Context) ={
    val rttype = visit(ast.expr,c).asInstanceOf[Type]
    val local = c.asInstanceOf[O].o.asInstanceOf[CType]
    val mthtype = lookupMethod(local.name,local.curMeth,List[Type](),global,3).get
    if(!typeCheck(mthtype,rttype)) throw TypeMismatchInStatement(ast) else c.asInstanceOf[O].o
  }
  override def visitNullLiteral(ast: NullLiteral.type, c: Context) = NullType.toString()
  override def visitSelfLiteral(ast: SelfLiteral.type, c: Context) = {
    val e = c.asInstanceOf[O].o.asInstanceOf[CType]
    CType(e.name,e.parent,"",e.memlist,e.curMeth)
  }
}
trait Utils extends Context{
  def lookup[T](name:String,lst:List[T],func:T=>String):Option[T] = 
  lst match {
    case List()=>None
    case h::t => if(func(h)==name) Some(h) else lookup(name,t,func)
  }
 def lookupClass(cl:String, list:List[CType]):Option[CType] = {
   list match{
     case List() => None
     case h::t => if(cl == h.name) Some(h) else lookupClass(cl,t)
   }
 }
 def lookupField(cl:String,field:String,list:List[CType]):Option[Symbol]={
  lookupClass(cl,list) match{
    case None => throw Undeclared(Identifier,cl)
    case Some(classAtt) => classAtt.memlist.find(x=>x.name == field) match{
      case None=>{
        if(classAtt.parent == "")throw Undeclared(Attribute,field) else lookupField(classAtt.parent,field,list)
      }
      case Some(a) => Some(a)
    }
  }
 }
 def lookupMethod(cl:String,meth:String,parType: List[Type],list:List[CType], stt: Int ):Option[Type]={
   // stt = 1 la callExpr = 2 la callStament = 0 la new
 
   
   lookupClass(cl,list) match{
     case None => {
       throw Undeclared(Identifier,cl)
     }
     case Some(classAtt) => classAtt.memlist.find(x=> x.name == meth) match{
       case None => {//None
         
         if(classAtt.parent == "") throw Undeclared(Method,meth) else lookupMethod(classAtt.parent,meth,parType,list,stt)
         }
       case Some(method) => method match{
         case Symbol(_,MethodType(par,rt)) =>stt match { 
           case 1 => {//return Some(rt)
            
             if(typeCheck(par,parType)/*&& rt != VoidType*/) 
               Some(rt) 
             else
           if(classAtt.parent == "") {
             None} else lookupMethod(classAtt.parent,meth,parType,list,stt)
           }
           case 2 =>//  return Some(rt)
             if(typeCheck(par,parType)/*&& rt == VoidType*/) Some(rt) else
           if(classAtt.parent == "") None else lookupMethod(classAtt.parent,meth,parType,list,stt)
           case 3 => Some(rt)
         }
         case Symbol(name,t) => None
           //return Some(t)
         //throw Undeclared(Method,method.name)
       }
       
     }
   }
 }
 def lookupNew(cl:String,oldCl:String,meth:String,oldMethod:String,parType: List[Type],list:List[CType] ):Option[Type]={
  println(list)
   lookupClass(cl, list) match{
      case None => throw Undeclared(Class,cl)
      case Some(classAtt) => {//CType(classAtt.name,classAtt.parent,classAtt.memlist)
        classAtt.memlist.find(x=> x.name == meth) match{
       case None => 
//         if(classAtt.parent == ""){


         if(parType.length == 0 ) Some(lookupClass(oldCl,list).get) else {
         /*throw Undeclared(Method,oldMethod)*/
           
     println(classAtt)
          // if(findSubClass(oldCl,oldMethod,list)) Some(lookupClass(oldCl,list).get)
  //         else
         println("vo day ha")
           None} 
//         }
//          else  None//lookupNew(classAtt.parent,oldCl,classAtt.parent,oldMethod,parType,list)
       case Some(method) => method match{
         case Symbol(_,MethodType(par,_)) =>{ 
           if(typeCheck(par,parType)) Some(CType(classAtt.name,classAtt.parent,classAtt.subclass,classAtt.memlist,classAtt.curMeth)) else
             println("Co chuyen roi")   
             None
 //            if(classAtt.parent == ""){
//              None /*Undeclared(Method,oldMethod)*/}
//           else{
//             lookupNew(classAtt.parent,oldCl,classAtt.parent,oldMethod,parType,list)
//             }
         }
       case Symbol(name,t) =>{
         throw Undeclared(Method,oldMethod) }
       }
       }
      }
    }
 }
 def findSubClass(par:String,sub:String,list:List[CType]):Boolean={
   lookupClass(sub,list) match{
     case None => return false
     case Some(cl) =>{
       
       if(cl.parent == "") return false else{
         if(cl.parent == par) return true
         else findSubClass(par,cl.parent,list)
       }
     }
   }
 }
 def insertMemList(ast: String, global : List[CType], ls:List[String]):List[Symbol]={
   if(!ls.exists { _==ast})
   {
     lookupClass(ast,global) match{
      case Some(cl) => {
        val memlst = cl.memlist.asInstanceOf[List[Symbol]]
        if(cl.parent == "") memlst else memlst ++ insertMemList(cl.parent,global,ast::ls)
      }
      case None => throw Undeclared(Class, ast)
     }
   }
   else List[Symbol]()
 }
  def insertVar(newele:VarDecl,lst:List[(String,Type)])=
  {
     lookup(newele.variable.toString(),lst,(x:(String,Type))=>x._1) match{
      case Some(t) => throw Redeclared(Attribute, newele.variable.toString())
      case None => (newele.variable.toString())::lst
    }
  }
  def insertCons(newele:VarDecl,lst:List[(String,Type)])=
  {
     lookup(newele.variable.toString(),lst,(x:(String,Type))=>x._1) match{
      case Some(t) => throw Redeclared(Attribute, newele.variable.toString())
      case None => (newele.variable.toString())::lst
    }
  }
  def typeCheck(pt:Type,at:Type):Boolean = {pt == at | pt==FloatType&&at==IntType}
  def typeCheck(pt:List[Type],at:List[Type]):Boolean={
    if(pt.length != at.length) false
//    else true
    else if(pt.length==0) true
    else pt.zip(at).forall(x=>typeCheck(x._1,x._2))
  }
}
