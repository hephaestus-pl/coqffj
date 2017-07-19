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
  | CRefine: ClassName ->
    forall (fDecls:[FieldDecl]), NoDup (refs fDecls) -> ConstructorRefine -> 
    forall (mDecls:[MethodDecl]), NoDup (refs mDecls) ->
    forall (mRefines:[MethodRefinement]), NoDup (refs mRefines) ->
    ClassRefinement.

Instance CRefinementFeat: Referable ClassRefinement :={
  ref R :=
  match R with 
   | (CRefine cname _ _ _ _ _ _ _) => cname end
}.

(* We assume a fixed Class Table *)
Parameter CT: [ClassDecl].

(* And a fixed Refinement Table *)
Parameter RT: env ([ClassRefinement]).

Fixpoint refinements_of' (C: ClassName) (RT': env ([ClassRefinement])) : [FeatureName * ClassRefinement]:=
  match RT' with
  | nil => nil
  | (f_name, crs) :: RT_tail => 
    match (find C crs) with
    | None => (refinements_of' C RT_tail)
    | Some cr => (f_name, cr) :: (refinements_of' C RT_tail)
    end
  end.

Definition refinements_of (C: ClassName) := refinements_of' C RT.
Inductive RefinementName: Type := 
  | RName : FeatureName -> ClassName -> RefinementName .
Notation "C @ feat" := (RName feat C) (at level 30).


Instance RNameRef : Referable RefinementName :={
  ref R := 
  match R with RName _ cname => cname end
}.

Instance RefinementsReferable: Referable (FeatureName * ClassRefinement) :={
  ref R :=
    match R with
    | (f_name, cr) => f_name
    end
}.

Definition feature_name (R: RefinementName) :=
  match R with RName fname _ => fname end.

Fixpoint get_decl (f_name: FeatureName) (Rs: [FeatureName * ClassRefinement]) :=
  match Rs with
  | nil => None 
  | (f_name', cr) :: xs => 
    if (beq_id f_name f_name') 
    then Some cr
    else get_decl f_name xs
  end.

Definition find_refinement_func (R: RefinementName): option ClassRefinement :=
    match R with C @ feat =>
    match refinements_of C with Rs =>
    match get_decl feat Rs with
    | Some RDecl => Some RDecl
    | None => None
    end end end.

Inductive find_refinement (R: RefinementName) (RDecl: ClassRefinement): Prop :=
  | R_Find : forall C feat Rs,
    R = C @ feat ->
    refinements_of C = Rs ->
    get_decl feat Rs = Some RDecl ->
    find_refinement R RDecl.

Hint Unfold find_refinement_func.

Lemma refinements_same_name: forall C,
  Forall (fun R => C = ref R) (map snd (refinements_of C)).
Proof.
  Hint Resolve beq_id_eq. Hint Rewrite find_ref_inv.
  intros.
  unfold refinements_of.
  induction RT. crush.
  destruct a. simpl in *. 
  assert ({(exists x, find C l = Some x)} + {find C l= None}). apply find_dec.
  destruct H. destruct e0. rewrite H.
  rewrite map_cons. simpl. constructor. crush. apply find_ref_inv in H. crush.
  auto.
  rewrite e0. auto.
Qed.

Lemma get_decl_In: forall rs CR feat,
  get_decl feat rs = Some CR ->
  In CR (map snd rs).
Proof.
  intros. induction rs. crush.
  simpl in *. destruct a.
  case (beq_id feat f) in H.
  inversion H. auto. right; auto.
Qed.

Lemma find_refinement_same_refinement: forall R CR, 
  find_refinement R CR ->
  ref R = ref CR.
Proof.
  induction 1. subst. 
  lets ?H: refinements_same_name C.
  rewrite Forall_forall in H. apply get_decl_In in H1.
  apply H in H1. crush.
Qed.

Lemma get_decl_dec: forall f cr,
  {x | get_decl f cr = Some x} + {get_decl f cr = None}.
Proof.
  intros. induction cr. crush.
  destruct IHcr. destruct a.
  destruct (beq_id_dec) with f f0. subst.
  left. simpl. exists c. rewrite beq_id_refl. auto.
  left. simpl. rewrite not_eq_beq_id_false; auto.
  destruct a. 
  destruct (beq_id_dec) with f f0. subst.
  left. simpl. exists c. rewrite beq_id_refl. auto.
  right. simpl. rewrite not_eq_beq_id_false; auto.
Qed.

Lemma find_refinement_reflected: forall R CR,
  find_refinement R CR <-> find_refinement_func R = Some CR.
Proof.
  intros. split. intros.
  destruct H. crush.
  intros.
  unfold find_refinement_func in H. destruct R.
  destruct get_decl_dec with f (refinements_of c). destruct s.
  rewrite e in H. eapply R_Find; crush.
  rewrite e in H; crush.
Qed.

Lemma find_refinement_dec: forall R,
  {exists CR, find_refinement R CR} + {forall CR, ~find_refinement R CR}.
Proof.
  intros.
  assert ({exists CR', find_refinement_func R = Some CR'} + {find_refinement_func R = None}).
  destruct R.
  destruct find_dec with (refinements_of c) f;  unfold find_refinement_func;
  destruct (get_decl f (refinements_of c)).
  left.  destruct e. eexists; crush.
  right. crush. left. eexists; crush. auto.
  destruct H. left. destruct e. exists x. apply find_refinement_reflected; auto.
  right. intros_all. apply find_refinement_reflected in H. crush.
Qed.
