Require Import String.
Require Import FJ.Lists.
Require Import FJ.Base.
(* We will use Notation to make automation easier
 * This will be the notation to be similar with haskell *)
Notation "'[' X ']'" := (list X) (at level 40).

Definition ClassName := id.
Parameter Object: ClassName.

Definition Var := id.
Parameter this: Var.

Inductive Argument :=
  | Arg : id -> Argument.

Inductive FormalArg :=
  | FArg : ClassName -> id -> FormalArg.

Instance FargRef : Referable FormalArg :={
  ref farg := 
    match farg with 
   | FArg _ id => id end
}.

Definition fargType (f: FormalArg):ClassName := 
  match f with FArg t _ => t end.

Inductive FieldDecl :=
  | FDecl : ClassName -> id -> FieldDecl.

Instance FieldRef : Referable FieldDecl :={
  ref fdecl := 
    match fdecl with 
   | FDecl _ id => id end
}.

Definition fieldType (f: FieldDecl): ClassName := 
  match f with FDecl t _ => t end.

Inductive Exp : Type :=
  | ExpVar : Var -> Exp
  | ExpFieldAccess : Exp -> id -> Exp
  | ExpMethodInvoc : Exp -> id -> [Exp] -> Exp
  | ExpCast : ClassName -> Exp -> Exp
  | ExpNew : id -> [Exp] -> Exp.

Inductive Assignment :=
  | Assgnmt : Exp -> Exp -> Assignment.


Inductive Constructor :=
  | KDecl : id -> [FormalArg] -> [Argument] -> [Assignment] -> Constructor.

Inductive ConstructorRefine :=
  | KRefine : id -> [FormalArg] -> [Argument] -> [Assignment] -> ConstructorRefine.


Inductive MethodDecl :=
  (* MDecl is the return of the method, its name and nonduplicate list of formal args *)
  | MDecl : ClassName -> id -> forall (fargs: [FormalArg]), NoDup (this :: refs fargs) -> Exp -> MethodDecl
  (* MRefine is the same *)
  | MRefine : ClassName -> id -> forall (fargs: [FormalArg]), NoDup (this :: refs fargs) -> Exp -> MethodDecl
.


Instance MDeclRef : Referable MethodDecl :={
  ref mdecl := 
    match mdecl with 
   | MDecl _ id _ _ _ => id
   | MRefine _ id _ _ _ => id end
}.

Inductive ClassDecl :=
  (* CDecl is the name of the class, the superclass, non duplicate fields,
  constructor and non duplicate methods *)
  | CDecl: id -> ClassName -> 
    forall (fDecls:[FieldDecl]), NoDup (refs fDecls) -> Constructor -> 
    forall (mDecls:[MethodDecl]), NoDup (refs mDecls) -> ClassDecl.

Inductive ClassRefinement :=
  (* CRefine is the name of the class, the refinement name
  and the refinement ordinal used to build the refinement chain
  , non duplicate fields,
  constructor and non duplicate methods *)
  | CRefine: id -> id -> nat ->
    forall (fDecls:[FieldDecl]), NoDup (refs fDecls) -> ConstructorRefine -> 
    forall (mDecls:[MethodDecl]), NoDup (refs mDecls) -> ClassRefinement.

Inductive Class :=
  | CD : ClassDecl -> Class
  | CR : ClassRefinement -> Class.

Instance CRef : Referable Class :={
  ref cdecl := 
    match cdecl with 
   | CD (CDecl id _ _ _ _ _ _) => id
   | CR (CRefine id _ _ _ _ _ _ _) => id end
}.

Inductive Program :=
  | CProgram : forall (cDecls: [Class]), NoDup (refs cDecls) -> Exp -> Program.
