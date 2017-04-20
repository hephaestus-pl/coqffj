Require Import String.
Require Import FFJ.Lists.
Require Import FFJ.Base.

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

Inductive RefinementName: Type :=
  | RName : ClassName -> FeatureName -> RefinementName.

Notation "C @ Feat" := (RName C Feat) (at level 30).
Parameter ObjectRefinement : RefinementName.

Class ClassNameRef (A: Set):={
  class_name : A -> id
}.

Instance RefinementNameCName: ClassNameRef RefinementName :={
  class_name C :=
  match C with
  | (RName i _) => i end
}.

Instance RefinementNameFeature: Referable RefinementName :={
  ref C :=
  match C with 
   | (RName _ feat) => feat end
}.

Inductive ClassDecl :=
  (* CDecl is the name of the class, the superclass, non duplicate fields,
  constructor and non duplicate methods *)
  | CDecl: ClassName -> ClassName -> 
    forall (fDecls:[FieldDecl]), NoDup (refs fDecls) -> Constructor -> 
    forall (mDecls:[MethodDecl]), NoDup (refs mDecls) -> ClassDecl.

Instance CDeclRef : Referable ClassDecl :={
  ref cdecl := 
    match cdecl with 
   | CDecl cref _ _ _ _ _ _ => cref end
}.

Inductive ClassRefinement :=
  (* CRefine is the name of the class
  , non duplicate fields,
  constructor and non duplicate methods *)
  | CRefine: RefinementName ->
    forall (fDecls:[FieldDecl]), NoDup (refs fDecls) -> ConstructorRefine -> 
    forall (mDecls:[MethodDecl]), NoDup (refs mDecls) ->
    forall (mRefines:[MethodRefinement]), NoDup (refs mRefines) ->
    ClassRefinement.

Instance CRefinementCName: ClassNameRef ClassRefinement :={
  class_name CR := 
  match CR with 
  | (CRefine (RName cname _) _ _ _ _ _ _ _) => cname
  end
}.

Instance CRefinementFeat: Referable ClassRefinement :={
  ref R :=
  match R with 
   | (CRefine Cref _ _ _ _ _ _ _) => ref Cref end
}.

Instance CRefinementOrCName: ClassNameRef (ClassName + RefinementName):={
  class_name Cl :=
  match Cl with
  | inl C => C
  | inr R => class_name R
  end
}.

Inductive Program :=
  | CProgram : forall (cDecls: [ClassDecl]), NoDup (refs cDecls) -> Exp -> Program.

(* We assume a fixed Class Table *)
Parameter CT: [ClassDecl].

(* And a fixed Refinement Table *)
Parameter RT: [ClassRefinement].

Definition refinements_of (C: ClassName) :=
  filter (fun R => beq_id C (class_name R)) RT.

Inductive find_refinement (R: RefinementName) (RDecl: ClassRefinement): Prop :=
  | R_Find : forall C feat Rs,
    R = C @ feat ->
    refinements_of C = Rs ->
    find feat Rs = Some RDecl ->
    find_refinement R RDecl.

Lemma refinements_same_name: forall C,
  Forall (fun R => C = (class_name R)) (refinements_of C).
Proof.
  Hint Resolve beq_id_eq.
  intros. 
  unfold refinements_of.
  apply Forall_forall. intros.
  apply filter_In in H. crush.
Qed.

Lemma find_refinement_same_refinement: forall R CR, 
  find_refinement R CR ->
  class_name R = class_name CR /\ ref R = ref CR.
Proof.
  induction 1. subst. 
  lets ?H: refinements_same_name C. 
destruct CR as [r]; destruct r; simpl in *.
  rewrite Forall_forall in H.
  specialize H with (CRefine (c0 @ f) fDecls n c mDecls n0 mRefines n1).
  split. apply find_in in H1. apply H in H1. auto.
  apply find_ref_inv in H1. eauto.
Qed.