Require Import String.
Require Import Relations Decidable.
Require Import FFJ.Base.
Require Import FFJ.Syntax.
Require Import Coq.Program.Basics.

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
    find C CT = Some (CDecl C D fs noDupfs K mds noDupMds) ->
    C <: D
where "C '<:' D" := (Subtype C D).
Hint Constructors Subtype.

Tactic Notation "subtype_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "S_Refl" | Case_aux c "S_Trans" 
  | Case_aux c "S_Decl"].

Inductive pred: RefinementName -> RefinementName -> Prop :=
  | P_Refine : forall C Rs feat n CR,
    refinements_of C = Rs ->
    find_where feat (refs Rs) = Some (S n) ->
    nth_error Rs n = Some CR ->
    pred (C @ feat) (class_name CR @ ref CR).

(* pred is just the inverse of succ
Inductive succ (Cl: ClassName + RefinementName) (R: RefinementName): Prop :=
  | C_pred: 
    pred R Cl ->
    succ Cl R.
*)
(* Refinement is the transitive closure of succ 
Reserved Notation "C <<: D" (at level 40).
Inductive Refinement: ClassName + RefinementName -> RefinementName -> Prop :=
  | R_Trans: forall C C' C'',
    succ C C' ->
    succ (inr C') C'' ->
    C <<: C''
  | R_succ : forall C C',
    succ C C' ->
    C <<: C'
where "C <<: C'" := (Refinement C C').
*)

Definition last_refinement (C: ClassName): option RefinementName :=
  match last_error (refinements_of C) with
  | Some R => Some (class_name R @ ref R)
  | NOne => None
  end.

Definition first_refinement (R: RefinementName) : Prop := forall S, ~pred R S.
(*
Lemma last_refinement_correct: forall C R,
  last_refinement C = Some R <-> no_suc (inr (class_name R @ ref R)).
Proof. (* Need to impose that there are no duplicated features *)
Admitted.
*)

Inductive fields_refinement : RefinementName -> [FieldDecl] -> Prop :=
  | F_Refine: forall R S fs fpred noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines,
    pred R S ->
    find_refinement R (CRefine R fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines) ->
    fields_refinement S fpred ->
    NoDup (refs (fpred ++ fs)) ->
    fields_refinement R (fpred ++ fs)
  | F_First: forall R fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines,
    first_refinement R ->
    find_refinement R (CRefine R fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines) ->
    fields_refinement R fs.

Hint Constructors pred.
Hint Unfold first_refinement.

Inductive fields : ClassName -> [FieldDecl] -> Prop :=
  | F_Obj : fields Object nil
  | F_Decl : forall C S D fs fs'' noDupfs K mds noDupMds fs', 
     find C CT = Some (CDecl C D fs noDupfs K mds noDupMds) ->
     last_refinement C = Some S ->
     fields_refinement S fs'' ->
     fields D fs' ->
     NoDup (refs (fs' ++ fs ++ fs'')) ->
     fields C (fs' ++ fs ++ fs'')
  | F_Decl_NoRefine : forall C D fs noDupfs K mds noDupMds fs', 
     find C CT = Some (CDecl C D fs noDupfs K mds noDupMds) ->
     last_refinement C = None ->
     fields D fs' ->
     NoDup (refs (fs' ++ fs)) ->
     fields C (fs' ++ fs).
Tactic Notation "fields_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "F_Obj" | Case_aux c "F_Decl"| Case_aux c "F_Decl_NoRefine"].

(*
Inductive rfields : ClassName + RefinementName -> [FieldDecl] -> Prop :=
  | RF_Decl : forall C D fs noDupfs K mds noDupMds fs',
     find C CT = Some (CDecl C D fs noDupfs K mds noDupMds) ->
     fields D fs' ->
     NoDup (refs (fs' ++ fs)) ->
     rfields (inl C) (fs'++fs)  
  | RF_Refine : forall R P fs noDupfs K mds noDupMds fs' Mrs noDupMrs,
     find_refinement R (CRefine R fs noDupfs K mds noDupMds Mrs noDupMrs) ->
     pred R P ->
     rfields P fs' ->
     NoDup (refs (fs' ++ fs)) ->
     rfields (inr R) (fs'++fs).
*)

Reserved Notation "'mtype_r(' m ',' R ')' '=' c '~>' c0" (at level 40, c at next level).
Inductive mtype_refinement (m: id) (R: RefinementName) (Bs: [ClassName]) (B: ClassName): Prop :=
  | mtyr_decl_ok : forall fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines fargs noDupfargs e,
              find_refinement R (CRefine R fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines) ->
              find m mDecls = Some (MDecl B m fargs noDupfargs e) ->
              map fargType fargs = Bs ->
              mtype_r(m, R) = Bs ~> B
  | mtyr_refinement_ok : forall fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines fargs noDupfargs e,
              find_refinement R (CRefine R fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines) ->
              find m mDecls = None ->
              find m mRefines = Some (MRefine B m fargs noDupfargs e) ->
              map fargType fargs = Bs ->
              mtype_r(m, R) = Bs ~> B
  | mtyr_pred: forall S fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines,
              find_refinement R (CRefine R fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines) ->
              find m mDecls = None  ->
              find m mRefines = None->
              pred R S ->
              mtype_r(m, S) = Bs ~> B ->
              mtype_r(m, R) = Bs ~> B
  where "'mtype_r(' m ',' R ')' '=' cs '~>' c0"
        := (mtype_refinement m R cs c0).

Reserved Notation "'mtype(' m ',' D ')' '=' c '~>' c0" (at level 40, c at next level).
Inductive m_type (m: id) (C: ClassName) (Bs: [ClassName]) (B: ClassName) : Prop:=
  | mty_ok : forall D Fs K Ms noDupfs noDupMds fargs noDupfargs e,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
              find m Ms = Some (MDecl B m fargs noDupfargs e) ->
              map fargType fargs = Bs ->
              (forall S xs' e', last_refinement C = Some S ->
                                ~ mtype_r(m, S) = xs' ~> e') ->
              mtype(m, C) = Bs ~> B
  | mty_no_override: forall D Fs K Ms noDupfs noDupMds,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
              find m Ms = None ->
              (forall S Bs' B', last_refinement C = Some S -> ~mtype_r(m, S) = Bs' ~> B') ->
              mtype(m, D) = Bs ~> B ->
              mtype(m, C) = Bs ~> B
  | mty_refinement: forall D S Fs K Ms noDupfs noDupMds,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
              find m Ms = None ->
              last_refinement C = Some S ->
              mtype_r(m, S) = Bs ~> B ->
              mtype(m, C) = Bs ~> B
  where "'mtype(' m ',' D ')' '=' cs '~>' c0"
        := (m_type m D cs c0).

Tactic Notation "mtype_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "mty_ok"         | Case_aux c "mty_no_override"
  | Case_aux c "mty_refinement" ].

Reserved Notation "'mbody_r(' m ',' R ')' '=' xs 'o' e" (at level 40, xs at next level).
Inductive mbody_refinement (m: id) (R: RefinementName) (xs: [id]) (e: Exp): Prop :=
  | mbodyr_ok : forall fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines fargs noDupfargs B,
              find_refinement R (CRefine R fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines) ->
              find m mDecls = Some (MDecl B m fargs noDupfargs e) ->
              refs fargs = xs ->
              mbody_r(m, R) = xs o e
  | mbodyr_refine : forall fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines fargs noDupfargs B,
              find_refinement R (CRefine R fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines) ->
              find m mDecls = None ->
              find m mRefines = Some (MRefine B m fargs noDupfargs e) ->
              refs fargs = xs ->
              mbody_r(m, R) = xs o e
  | mbodyr_pred: forall S fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines,
              find_refinement R (CRefine R fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines) ->
              find m mDecls = None ->
              find m mRefines = None->
              pred R S ->
              mbody_r(m, S) = xs o e ->
              mbody_r(m, R) = xs o e
  where "'mbody_r(' m ',' R ')' '=' xs 'o' e"
        := (mbody_refinement m R xs e).

Reserved Notation "'mbody(' m ',' D ')' '=' xs 'o' e" (at level 40, xs at next level).
Inductive m_body (m: id) (C: ClassName) (xs: [ClassName]) (e: Exp) : Prop:=
  | mbody_ok : forall D Fs K Ms noDupfs noDupMds C0 fargs noDupfargs,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
              find m Ms = Some (MDecl C0 m fargs noDupfargs e) ->
              refs fargs = xs ->
              (forall S xs' e', last_refinement C = Some S ->
                                ~ mbody_r(m, S) = xs' o e') ->
              mbody(m, C) = xs o e
  | mbody_no_override: forall D Fs K Ms noDupfs noDupMds,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
              find m Ms = None ->
              (forall S xs' e', last_refinement C = Some S ->
                                ~ mbody_r(m, S) = xs' o e') ->
              mbody(m, D) = xs o e ->
              mbody(m, C) = xs o e
  | mbody_last : forall S D Fs K Ms noDupfs noDupMds,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
              find m Ms = None ->
              last_refinement C = Some S -> 
              mbody_r(m, S) = xs o e ->
              mbody(m, C) = xs o e
  where "'mbody(' m ',' D ')' '=' xs 'o' e" := (m_body m D xs e).

Tactic Notation "mbdy_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "mbdy_ok" | Case_aux c "mbdy_no_override"
  | Case_aux c "mbdy_last" ].

Hint Constructors mbody_refinement m_body mtype_refinement m_type.

Inductive override (m: id) (D: ClassName) (Cs: [ClassName]) (C0: ClassName): Prop :=
  | C_override : 
    (forall Ds D0, mtype(m, D) = Ds ~> D0 -> (Ds = Cs /\ C0 = D0)) ->
    override m D Cs C0.

Inductive introduce (m: id) (R: RefinementName): Prop :=
  | I_Refinement : forall S,
    pred R S ->
    (forall Ds D0, ~ mtype_r(m, S) = Ds ~> D0) ->
    introduce m R
  | I_Class : forall C feat,
    first_refinement R -> R = C @ feat ->
    (forall Ds D0, ~ mtype(m, C) = Ds ~> D0) ->
    introduce m R.

Inductive extend (m: id) (R: RefinementName) (Cs: [ClassName]) (C0: ClassName): Prop :=
  | E_Refinement : forall Ds D0,
    (mtype_r(m, R) = Ds ~> D0 -> (Cs = Cs /\ C0 = D0)) ->
    extend m R Cs C0.

Lemma find_class_same_ref: forall C CD,
  find C CT = Some CD ->
  C = ref CD.
Proof.
  intros. apply find_ref_inv in H. auto.
Qed.

Lemma pred_same_cname: forall Cl R,
  pred Cl R ->
  class_name Cl = class_name R.
Proof.
  induction 1; crush. destruct CR. destruct r.
  lets ?H: refinements_same_name C.
  apply nth_error_In in H1. rewrite Forall_forall in H. eapply H in H1.
  eauto.
Qed.

(*
Lemma refinement_same_cname : forall R Cl,
  Cl <<: R ->
  class_name R = class_name Cl.
Proof.
  destruct 1.  apply pred_same_cname in H.
  repeat match goal with
  | H: pred ?R ?C |- _ => apply pred_same_cname in H
  end; crush.
Qed. 
*)
Hint Resolve find_class_same_ref pred_same_cname.
