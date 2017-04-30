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

Fixpoint pred_func (R: RefinementName): option RefinementName :=
  match R with C @ feat =>
  match find_where feat (refs (refinements_of C)) with
  | None => None
  | Some 0 => None
  | Some (S n) => match nth_error (refinements_of C) n with
    | None => None
    | Some CR => Some (class_name CR @ ref CR)
  end end end.

Definition last_refinement (C: ClassName): option RefinementName :=
  match last_error (refinements_of C) with
  | Some R => Some (class_name R @ ref R)
  | None => None
  end.

Definition first_refinement (R: RefinementName) : Prop := forall S, ~pred R S.

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

Inductive mnotin_refinement (m: id) (R: RefinementName) : Prop :=
  | notin_first : forall fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines,
              find_refinement R (CRefine R fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines) ->
              find m mDecls = None ->
              find m mRefines = None ->
              first_refinement R ->
              mnotin_refinement m R
  | notin_pred : forall S fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines,
              find_refinement R (CRefine R fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines) ->
              find m mDecls = None ->
              find m mRefines = None ->
              pred R S -> 
              mnotin_refinement m S ->
              mnotin_refinement m R.

Definition mnotin_last_refinement (m: id) (C: ClassName) :=
  forall R, last_refinement C = Some R -> mnotin_refinement m R.
SearchAbout bool.

(*
Fixpoint mnotin_refinement_bool (m:id) (R: RefinementName): bool :=
  match find_refinement_func R with 
  | None => false
  | Some (CRefine R fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines) =>
  match find m mDecls with
  | Some _ => false
  | None => match find m mRefines with
    | Some _ => false
    | None => match pred_func R with
      | None => true
      | Some P => mnotin_refinement_bool m P
      end
    end
  end end.
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

Tactic Notation "mtype_r_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "mtyr_decl_ok"         | Case_aux c "mtyr_refinement_ok"
  | Case_aux c "mtyr_pred" ].

Reserved Notation "'mtype(' m ',' D ')' '=' c '~>' c0" (at level 40, c at next level).
Inductive m_type (m: id) (C: ClassName) (Bs: [ClassName]) (B: ClassName) : Prop:=
  | mty_ok : forall D Fs K Ms noDupfs noDupMds fargs noDupfargs e,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
              find m Ms = Some (MDecl B m fargs noDupfargs e) ->
              map fargType fargs = Bs ->
              mnotin_last_refinement m C ->
              mtype(m, C) = Bs ~> B
  | mty_no_override: forall D Fs K Ms noDupfs noDupMds,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
              find m Ms = None ->
              mnotin_last_refinement m C ->
              mtype(m, D) = Bs ~> B ->
              mtype(m, C) = Bs ~> B
  | mty_refinement: forall D S Fs K Ms noDupfs noDupMds,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
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

Tactic Notation "mbdy_r_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "mbodyr_ok" | Case_aux c "mbodyr_refine"
  | Case_aux c "mbodyr_pred" ].

Reserved Notation "'mbody(' m ',' D ')' '=' xs 'o' e" (at level 40, xs at next level).
Inductive m_body (m: id) (C: ClassName) (xs: [ClassName]) (e: Exp) : Prop:=
  | mbody_ok : forall D Fs K Ms noDupfs noDupMds C0 fargs noDupfargs,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
              find m Ms = Some (MDecl C0 m fargs noDupfargs e) ->
              refs fargs = xs ->
              mnotin_last_refinement m C ->
              mbody(m, C) = xs o e
  | mbody_no_override: forall D Fs K Ms noDupfs noDupMds,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
              find m Ms = None ->
              mnotin_last_refinement m C ->
              mbody(m, D) = xs o e ->
              mbody(m, C) = xs o e
  | mbody_last : forall S D Fs K Ms noDupfs noDupMds,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
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
  | E_Refinement : 
    (forall Ds D0, mtype_r(m, R) = Ds ~> D0 -> (Cs = Cs /\ C0 = D0)) ->
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

Hint Resolve find_class_same_ref pred_same_cname.
