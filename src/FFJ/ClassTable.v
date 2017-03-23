Require Import String.
Require Import Relations Decidable.
Require Import FFJ.Base.
Require Import FFJ.Syntax.

(* From our CT we can derive a subtype relation which is the reflexive
  and transitive closure of the subclass relation.
  i.e. A class relates with any of its superclass via the Subtype relation *)
Reserved Notation "C '<:' D " (at level 40).
Inductive Subtype : ClassName -> ClassName -> Prop :=
  | S_Refl: forall C: ClassName, C <: C
  | S_Trans: forall (C D E: ClassName), 
    C <: D -> 
    D <: E -> 
    C <: E
  | S_Decl: forall C D fs noDupfs K mds noDupMds,
    find_class C = Some (CD (CDecl C D fs noDupfs K mds noDupMds )) ->
    (ref C) <: D
where "C '<:' D" := (Subtype C D).
Hint Constructors Subtype.

Tactic Notation "subtype_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "S_Refl" | Case_aux c "S_Trans" 
  | Case_aux c "S_Decl"].
Print Nat.divide.

(* We can also fetch the next refinement in the refinement chain.
   For this, we encode a feature by a number of zeros (n and m) on the right of a ClassName.
   So if we have a refinement of the class C in the refinement 00 it will be encoded as
   CRefine (C * 100) fDecls ...
   succ relates a Class with its nearest refinement, 
   i.e., that have the smallest number of zeros.  
   Is it possible to encode this smallest property any nicer?
 *)
Inductive succ (C: ClassReference) (C': ClassReference): Prop :=
  | C_succ : forall C'decl feat feat' n,
    feat = feature C ->
    find_where feat RT = Some n ->
    nth_error RT (S n) = Some feat' ->
    find_class (CRef (ref C) feat') = Some C'decl ->
    ref C'decl = ref C' ->
    succ C C'.

(* pred is just the inverse of succ *)
Inductive pred (C: ClassReference) (C': ClassReference): Prop :=
  | C_pred: 
    succ C' C ->
    pred C C'.

(* Refinement is the transitive closure of succ *)
Reserved Notation "C <<: D" (at level 40).
Inductive Refinement: ClassReference -> ClassReference -> Prop :=
  | R_Trans: forall C C' C'',
    succ C C' ->
    succ C' C'' ->
    C <<: C''
  | R_succ : forall C C',
    succ C C' ->
    C <<: C'
where "C <<: C'" := (Refinement C C').

(* Last is the most specific refinement *)
Inductive last (C: ClassReference) (C': ClassReference): Prop:=
  | C_Last:
    C <<: C' ->
    (forall C'', ~succ C' C'') ->
    last C C'.

Inductive class_declaration : ClassReference -> Prop :=
  | get_decl : forall C D fs noDupfs K mds noDupMds,
     find_class C = Some (CD (CDecl C D fs noDupfs K mds noDupMds)) ->
    class_declaration C.

Hint Constructors succ Refinement last class_declaration.

Inductive fields : ClassReference -> [FieldDecl] -> Prop :=
 | F_Obj : forall feat, fields (Object @ feat) nil
 | F_Decl : forall C D S fs fsuc noDupfs K mds noDupMds fs',
     find_class C = Some (CD (CDecl C (ref D) fs noDupfs K mds noDupMds)) ->
     class_declaration D ->
     succ C S ->
     fields S fsuc ->
     fields D fs' ->
     NoDup (refs (fs' ++ fs ++ fsuc)) ->
     fields C (fs' ++ fs ++ fsuc)
  | F_Refine: forall C S fs fsuc noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines,
     find_class C = Some (CR (CRefine C fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines)) ->
     succ C S ->
     fields S fsuc ->
     NoDup (refs (fs ++ fsuc)) ->
     fields C (fs ++ fsuc).
Tactic Notation "fields_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "F_Obj" | Case_aux c "F_Decl"
  | Case_aux c "F_Refine" ].

Inductive rfields : ClassReference -> [FieldDecl] -> Prop :=
 | RF_Obj : forall feat, rfields (Object @ feat) nil
 | RF_Decl : forall C D S fs noDupfs K mds noDupMds fs',
     find_class C = Some (CD (CDecl C (ref D) fs noDupfs K mds noDupMds)) ->
     class_declaration D ->
     succ C S ->
     fields D fs' ->
     NoDup (refs (fs' ++ fs)) ->
     rfields C (fs' ++ fs)
  | RF_Refine: forall C S fs fpred noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines,
     find_class C = Some (CR (CRefine C fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines)) ->
     pred C S ->
     fields S fpred ->
     NoDup (refs (fpred ++ fs)) ->
     rfields C (fpred ++ fs).
Tactic Notation "rfields_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "RF_Obj" | Case_aux c "RF_Decl"
  | Case_aux c "RF_Refine" ].

Inductive methodDecl_in_succs (m: id) (C: ClassReference) : Prop :=
  | MD_in_succ : forall S fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines B fargs noDupfargs e,
              succ C S ->
              find_class S = Some (CR (CRefine S fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines)) ->
              find m mDecls = Some (MDecl B m fargs noDupfargs e) ->
              methodDecl_in_succs m C
  | MD_notin_succ: forall S SS fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines,
              succ C S ->
              find_class S = Some (CR (CRefine S fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines)) ->
              find m mDecls = None ->
              succ S SS ->
              methodDecl_in_succs m SS ->
              methodDecl_in_succs m C.


Inductive methodRefine_in_succs (m: id) (C: ClassReference) : Prop :=
  | MR_in_succ : forall S fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines B fargs noDupfargs e,
              succ C S ->
              find_class S = Some (CR (CRefine S fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines)) ->
              find m mRefines = Some (MRefine B m fargs noDupfargs e) ->
              methodRefine_in_succs m C
  | MR_notin_succ: forall S SS fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines,
              succ C S ->
              find_class S = Some (CR (CRefine S fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines)) ->
              find m mRefines = None ->
              succ S SS ->
              methodRefine_in_succs m SS ->
              methodRefine_in_succs m C.

Definition method_in_succs (m: id) (C: ClassReference)  := methodDecl_in_succs m C /\ methodRefine_in_succs m C.

Reserved Notation "'mtype(' m ',' D ')' '=' c '~>' c0" (at level 40, c at next level).
Inductive m_type (m: id) (C: ClassReference) (Bs: [ClassName]) (B: ClassName) : Prop:=
  | mty_ok : forall D Fs K Ms noDupfs noDupMds fargs noDupfargs e,
              find_class C = Some (CD (CDecl C D Fs noDupfs K Ms noDupMds)) ->
              find m Ms = Some (MDecl B m fargs noDupfargs e) ->
              map fargType fargs = Bs ->
              mtype(m, C) = Bs ~> B
  | mty_no_override: forall D Fs K Ms noDupfs noDupMds,
              find_class C = Some (CD (CDecl C (ref D) Fs noDupfs K Ms noDupMds)) ->
              class_declaration D ->
              find m Ms = None ->
              ~ methodDecl_in_succs m C ->
              mtype(m, D) = Bs ~> B ->
              mtype(m, C) = Bs ~> B
  | mty_no_override_no_succ: forall D S Fs K Ms noDupfs noDupMds,
              find_class C = Some (CD (CDecl C (ref D) Fs noDupfs K Ms noDupMds)) ->
              class_declaration D ->
              find m Ms = None ->
              succ C S ->
              mtype(m, S) = Bs ~> B ->
              mtype(m, C) = Bs ~> B
  | mty_refine : forall fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines Ms fargs noDupfargs e,
              find_class C = Some (CR (CRefine C fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines)) ->
              find m Ms = Some (MDecl B m fargs noDupfargs e) ->
              map fargType fargs = Bs ->
              mtype(m, C) = Bs ~> B
  | mty_succ: forall S fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines Ms,
              find_class C = Some (CR (CRefine C fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines)) ->
              find m Ms = None ->
              succ C S ->
              mtype(m, S) = Bs ~> B ->
              mtype(m, C) = Bs ~> B
  where "'mtype(' m ',' D ')' '=' cs '~>' c0"
        := (m_type m D cs c0).

Tactic Notation "mtype_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "mty_ok"                  | Case_aux c "mty_no_override"
  | Case_aux c "mty_no_override_no_succ" | Case_aux c "mty_refine"
  | Case_aux c "mty_succ" ].


Reserved Notation "'rmtype(' m ',' D ')' '=' c '~>' c0" (at level 40, c at next level).
Inductive rm_type (m: id) (C: ClassReference) (Bs: [ClassName]) (B: ClassName) : Prop:=
  | rmty_ok : forall D Fs K Ms noDupfs noDupMds fargs noDupfargs e,
              find_class C = Some (CD (CDecl C D Fs noDupfs K Ms noDupMds)) ->
              find m Ms = Some (MDecl B m fargs noDupfargs e) ->
              map fargType fargs = Bs ->
              rmtype(m, C) = Bs ~> B
  | rmty_refine : forall fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines Ms fargs noDupfargs e,
              find_class C = Some (CR (CRefine C fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines)) ->
              find m Ms = Some (MDecl B m fargs noDupfargs e) ->
              map fargType fargs = Bs ->
              rmtype(m, C) = Bs ~> B
  | rmty_no_extd: forall P fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines Ms,
              find_class C = Some (CR (CRefine C fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines)) ->
              find m Ms = None ->
              pred C P ->
              rmtype(m, P) = Bs ~> B ->
              rmtype(m, C) = Bs ~> B
  where "'rmtype(' m ',' D ')' '=' cs '~>' c0"
        := (rm_type m D cs c0).

Tactic Notation "mtype_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rmty_ok" | Case_aux c "rmty_refine"
  | Case_aux c "rmty_no_extd" ].

Reserved Notation "'mbody(' m ',' D ')' '=' xs 'o' e" (at level 40, xs at next level).
Inductive m_body (m: id) (C: ClassReference) (xs: [ClassName]) (e: Exp) : Prop:=
  | mbdy_ok : forall D Fs K Ms noDupfs noDupMds C0 fargs noDupfargs,
              find_class C = Some (CD (CDecl C D Fs noDupfs K Ms noDupMds)) ->
              find m Ms = Some (MDecl C0 m fargs noDupfargs e) ->
              refs fargs = xs ->
              ~ method_in_succs m C ->
              mbody(m, C) = xs o e
  | mbdy_no_override: forall D Fs K Ms noDupfs noDupMds,
              find_class C = Some (CD (CDecl C (ref D) Fs noDupfs K Ms noDupMds)) ->
              class_declaration D ->
              find m Ms = None ->
              ~ method_in_succs m C ->
              mbody(m, D) = xs o e ->
              mbody(m, C) = xs o e
  | mbdy_succ : forall S,
              succ C S ->
              mbody(m, S) = xs o e ->
              mbody(m, C) = xs o e
  | mbdy_refine_mdecl : forall Fs noDupfs Kr MDs noDupMds MRs noDupMrs C0 fargs noDupfargs,
              find_class C = Some (CR (CRefine C Fs noDupfs Kr MDs noDupMds MRs noDupMrs)) ->
              ~ method_in_succs m C ->
              find m MDs = Some (MDecl C0 m fargs noDupfargs e) ->
              refs fargs = xs ->
              mbody(m, C) = xs o e
  | mbdy_refine_mref : forall Fs noDupfs Kr MDs noDupMds MRs noDupMrs C0 fargs noDupfargs,
              find_class C = Some (CR (CRefine C Fs noDupfs Kr MDs noDupMds MRs noDupMrs)) ->
              ~ method_in_succs m C ->
              find m MRs = Some (MRefine C0 m fargs noDupfargs e) ->
              refs fargs = xs ->
              mbody(m, C) = xs o e
  | mbdy_refine_succ : forall S fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines,
              find_class C = Some (CR (CRefine C fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines)) ->
              succ C S ->
              mbody(m, S) = xs o e ->
              mbody(m, C) = xs o e
  where "'mbody(' m ',' D ')' '=' xs 'o' e" := (m_body m D xs e).

Tactic Notation "mbdy_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "mbdy_ok" | Case_aux c "mbdy_no_override"
  | Case_aux c "mbdy_succ" | Case_aux c "mbdy_refine_mdecl"
  | Case_aux c "mbdy_refine_mref" | Case_aux c "mbdy_refine_succ"].

Hint Constructors methodDecl_in_succs m_type m_body fields rfields.

Inductive override (m: id) (D: ClassReference) (Cs: [ClassName]) (C0: ClassName): Prop :=
  | C_override : forall Ds D0,
    (mtype(m, D) = Ds ~> D0 -> (Cs = Cs /\ C0 = D0)) ->
    override m D Cs C0.

(* Should I do this one in terms of method_in_succ also? 
  I really think it should be pred here 
*)
Inductive introduce (m: id) (C: ClassReference): Prop :=
  | C_introduce : forall S,
    succ C S ->
    (forall Ds D0, ~ mtype(m, S) = Ds ~> D0) ->
    introduce m C.

Inductive extend (m: id) (D: ClassReference) (Cs: [ClassName]) (C0: ClassName): Prop :=
  | C_extend : forall Ds D0,
    (rmtype(m, D) = Ds ~> D0 -> (Cs = Cs /\ C0 = D0)) ->
    extend m D Cs C0.

Lemma find_class_same_ref: forall C CDecl,
  find_class C = Some CDecl ->
  ref C = ref CDecl.
Proof.
  intros. unfold find_class in H. apply find_ref_inv in H. auto.
Qed.

Lemma succ_same_ref : forall R C,
  succ R C ->
  ref R = ref C.
Proof.
  induction 1. 
  apply find_class_same_ref in H2; crush.
Qed.

Lemma refinement_same_ref : forall R C,
  R <<: C ->
  ref R = ref C.
Proof.
  intros. induction H.
  rewrite succ_same_ref with C C'; eauto.
  rewrite succ_same_ref with C' C''; eauto.
  rewrite succ_same_ref with C C'; eauto.
Qed.