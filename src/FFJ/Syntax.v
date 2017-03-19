Require Import String.
Require Import FJ.Lists.
Require Import FJ.Base.
(* This will be the notation to be similar with haskell *)
Notation "'[' X ']'" := (list X) (at level 40).

(* We could use Inductive for ClassNames and Vars, 
 * but would make the other definitions cumbersome to deal with 
 * the special names Object and this.
 * ClassNames are our types.
 *)
Definition ClassName := id.
Parameter Object: ClassName.

(* Vars must appear only inside methods body *)
Definition Var := id.
Parameter this: Var.

Inductive Argument :=
  | Arg : id -> Argument.

(* FormalArg and FieldDecl is a ClassName (i.e. a type) and an id *)
Inductive FormalArg :=
  | FArg : ClassName -> id -> FormalArg.
Inductive FieldDecl :=
  | FDecl : ClassName -> id -> FieldDecl.

(* Referable essentialy means I can use the ref function
 * to retrieve the id of a value.
 * And it also gives me a nice function ´find´ for free.
 * See Util.Referable
*)
Instance FargRef : Referable FormalArg :={
  ref farg := 
    match farg with 
   | FArg _ id => id end
}.
Instance FieldRef : Referable FieldDecl :={
  ref fdecl := 
    match fdecl with 
   | FDecl _ id => id end
}.

(* fargType and fieldType are a means to retrieve the Type of the declarations *)
Definition fargType (f: FormalArg):ClassName := 
  match f with FArg t _ => t end.
Definition fieldType (f: FieldDecl): ClassName := 
  match f with FDecl t _ => t end.

(* Our expressions are Variables,
 * field acesses,
 * method invocations,
 * cast
 * and new
*)
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
  | MDecl : ClassName -> id -> forall (fargs: [FormalArg]), NoDup (this :: refs fargs) -> Exp -> MethodDecl.

Inductive MethodRefinement :=
| MRefine : ClassName -> id -> forall (fargs: [FormalArg]), NoDup (this :: refs fargs) -> Exp -> MethodRefinement
.


Instance MDeclRef : Referable MethodDecl :={
  ref mdecl := 
    match mdecl with 
   | MDecl _ id _ _ _ => id end
}.

Instance MRefineRef : Referable MethodRefinement :={
  ref mrefine := 
    match mrefine with 
   | MRefine _ id _ _ _ => id end
}.


(* The Name of a feature also encodes its order, taken from the "composition engine" 
 * In the paper they forbid the simbol '@' for classnames, and use it to create the name of a refinement,
 * which is className@featureName.
 * Since our classnames here are nats, we will forbid classnames divisible by 10.
 * This way a refinement of a class will be className * 10.
*)
Definition FeatureName := id.

Inductive ClassReference: Type :=
  | CRef : id -> FeatureName -> ClassReference.

Notation "C @ Feat" := (CRef C Feat) (at level 30).

Class Featurable (A: Set) :={
  feature : A -> FeatureName;
  get_feature : FeatureName -> list A -> list A := 
  fun key l => filter (fun x => beq_id key (feature x)) l
}.

Instance ClassDeclFeature: Referable ClassReference :={
  ref C :=
  match C with 
   | (CRef i _) => i end
}.

Instance ClassReferenceFeature: Featurable ClassReference :={
  feature C :=
  match C with 
   | (CRef _ f) => f end
}.


Inductive ClassDecl :=
  (* CDecl is the name of the class, the superclass, non duplicate fields,
  constructor and non duplicate methods *)
  | CDecl: ClassReference -> ClassName -> 
    forall (fDecls:[FieldDecl]), NoDup (refs fDecls) -> Constructor -> 
    forall (mDecls:[MethodDecl]), NoDup (refs mDecls) -> ClassDecl.

Instance CDeclRef : Referable ClassDecl :={
  ref cdecl := 
    match cdecl with 
   | CDecl cref _ _ _ _ _ _ => ref cref end
}.
Instance CDeclFeat : Featurable ClassDecl :={
  feature cdecl := 
    match cdecl with 
   | CDecl cref _ _ _ _ _ _ => feature cref end
}.
Inductive ClassRefinement :=
  (* CRefine is the name of the class
  , non duplicate fields,
  constructor and non duplicate methods *)
  | CRefine: ClassReference ->
    forall (fDecls:[FieldDecl]), NoDup (refs fDecls) -> ConstructorRefine -> 
    forall (mDecls:[MethodDecl]), NoDup (refs mDecls) ->
    forall (mRefines:[MethodRefinement]), NoDup (refs mRefines) ->
 ClassRefinement.

Instance CRefinementRef : Referable ClassRefinement :={
  ref cdecl := 
    match cdecl with 
   | (CRefine Cref _ _ _ _ _ _ _) => ref Cref end
}.
Instance CRefinementFeat : Featurable ClassRefinement :={
  feature cdecl := 
    match cdecl with 
   | (CRefine Cref _ _ _ _ _ _ _) => feature Cref end
}.

Inductive Class :=
  | CD : ClassDecl -> Class
  | CR : ClassRefinement -> Class.

Instance ClassRef : Referable Class :={
  ref Cl := 
    match Cl with 
   | CD Cd => ref Cd
   | CR Cr as Cref => ref Cr end
}.
Instance ClassFeat : Featurable Class :={
  feature Cl := 
    match Cl with 
   | CD Cd => feature Cd
   | CR Cr as Cref => feature Cr end
}.

Inductive Program :=
  | CProgram : forall (cDecls: [Class]), NoDup (refs cDecls) -> Exp -> Program.

(* We assume a fixed Class Table *)
Parameter CT: [Class].

(* The Refinement Table gives us the order in wich features will be applied  *)
Parameter RT: [FeatureName].
