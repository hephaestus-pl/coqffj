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

(* Constructor declaration \texttt{C(\={C}~\={f})\{super(\={f}); this.\={f}=\={f};\}} and a constructor refinement 
 * \texttt{refines~C(\={E}~\={h}, \={C}~\={f}) \{original(\={f}); this.\={f}=\={f};\}} introduces a constructor with 
 * for the class \texttt{C} with fields \texttt{\=f} of type \texttt{\=C}. The constructor declaration body is simply 
 * a list of assignment of the arguments with its correspondent field preceded by calling its superclass constructor with the correspondent arguments.
 * The constructor refinement only differs from constructor declaration that instead of calling the superclass constructor
 * it will call its predecessor constructor (denoted by \texttt{original}).
 *)
Inductive Constructor :=
  | KDecl : id -> [FormalArg] -> [Argument] -> [Assignment] -> Constructor.

Inductive ConstructorRefine :=
  | KRefine : id -> [FormalArg] -> [Argument] -> [Assignment] -> ConstructorRefine.

(* Method declaration \texttt{C~m~(\={C}~\={x})\ \{return~e;\}} and method refinement \texttt{refines C~m~(\={C}~\={x})\ \{return~e;\}} 
 * introduces a method \texttt{m} of return type \texttt{C} with arguments \texttt{\={C}~\={x}} and body \texttt{e}.
 * Method declarations should only appear inside a class declaration or a class refinement, whereas method refinement should only appear
 * inside a class refinement. There is such a distinction between method declaration and method refinement for allowing the type checker
 * to recognize the difference between method refinement and inadvertent overriding/replacement.
 *)
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

(* A class declaration \texttt{class\ C~extends~D\ \{\={C} \={f}; K \={M}\}} 
 * introduces a class \texttt{C} with superclass \texttt{D}. This class has fields \texttt{\=f}
 * of type \texttt{C}, a constructor \texttt{K} and methdos \texttt{\=M}. The fields of class \texttt{C}
 * is \texttt{\=f} added to the fields of its superclass \texttt{D}, all of them must have distinct names.
 * Methods, in the other, hand may override another superclass method with the same name.
 * Method override both in FJ and FFJ is basically method rewrite. 
 * Methods are uniquely identified by its name, i.e. overload is not supported.
 *)

Inductive ClassDecl :=
  | CDecl: ClassName -> ClassName -> 
    forall (fDecls:[FieldDecl]), NoDup (refs fDecls) -> Constructor -> 
    forall (mDecls:[MethodDecl]), NoDup (refs mDecls) -> ClassDecl.

Instance CDeclRef : Referable ClassDecl :={
  ref cdecl := 
    match cdecl with 
   | CDecl cref _ _ _ _ _ _ => cref end
}.

(* A class refinement \texttt{refines~class~R~\{\={C}~\={f};~KD~\={M}~\={MR}\}}
 * introduces a refinement of the class \texttt{C}. 
 * This refinement contains the fields  \texttt{\=f} of type \texttt{\=C}, 
 * a constructor refinement \texttt{KR}, methods declarations \texttt{\=M} and method refinements \texttt{\={MR}}.
 * Like class declarations, the fields of a class refinement \texttt{R} are added to the fields of its predecessor.
 *)
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

Definition find_refinement_func (R: RefinementName): option ClassRefinement :=
    match R with C @ feat =>
    match refinements_of C with Rs =>
    match find feat Rs with
    | Some RDecl => Some RDecl
    | None => None
    end end end.
Hint Unfold find_refinement_func.

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

Lemma find_refinement_reflected: forall R CR,
  find_refinement R CR <-> find_refinement_func R = Some CR.
Proof.
  intros. split. intros.
  destruct H. crush.
  intros.
  unfold find_refinement_func in H. destruct R.
  destruct find_dec with (refinements_of c) f. destruct e. rewrite H0 in H.
  eapply R_Find; crush. rewrite e in H. inversion H.
Qed.

Lemma find_refinement_dec: forall R,
  {exists CR, find_refinement R CR} + {forall CR, ~find_refinement R CR}.
Proof.
  intros.
  assert ({exists CR', find_refinement_func R = Some CR'} + {find_refinement_func R = None}).
  destruct R.
  destruct find_dec with (refinements_of c) f;  unfold find_refinement_func.
  left.  destruct e. eexists; crush.
  right. crush.
  destruct H. left. destruct e. exists x. apply find_refinement_reflected; auto.
  right. intros_all. apply find_refinement_reflected in H. crush.
Qed.
