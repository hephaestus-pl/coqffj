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

(* We can also fetch the next refinement in the refinement chain.
   For this, we encode a feature by a number of zeros (n and m) on the right of a ClassName.
   So if we have a refinement of the class C in the refinement 00 it will be encoded as
   CRefine (C * 100) fDecls ...
   succ relates a Class with its nearest refinement, 
   i.e., that have the smallest number of zeros.  
   Is it possible to encode this smallest property any nicer?
 *)
Inductive succ (Cl: ClassName + RefinementName) (R: RefinementName): Prop :=
  | Class_succ : forall C feat',
    Cl = inl C ->
    head (features (refinements_of C)) = Some feat' ->
    R = C @ feat' ->
    succ Cl R
  | Refine_succ : forall C Rs feat n feat',
    Cl = inr (C @ feat) ->
    refinements_of C = Rs ->
    find_where feat (features Rs) = Some n ->
    head (skipn (S n) (features Rs)) = Some feat' ->
    R = C @ feat' ->
    succ Cl R.

(* pred is just the inverse of succ *)
Inductive pred (R: RefinementName) (Cl: ClassName + RefinementName): Prop :=
  | C_pred: 
    succ Cl R ->
    pred R Cl.

(* Refinement is the transitive closure of succ *)
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

Definition last (R: ClassName + RefinementName) : Prop := forall S, ~succ R S.
    
Inductive fields_refinement : RefinementName -> [FieldDecl] -> Prop :=
  | F_Refine: forall R S C feat Rs fs fsuc noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines,
    R = C @ feat ->
    succ (inr R) S ->
    refinements_of C = Rs -> 
    find C Rs = Some (CRefine R fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines) ->
    fields_refinement S fsuc ->
    NoDup (refs (fs ++ fsuc)) ->
    fields_refinement R (fs ++ fsuc)
  | F_Last: forall R C feat Rs fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines,
    R = C @ feat ->
    last (inr R) ->
    refinements_of C = Rs -> 
    find C Rs = Some (CRefine R fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines) ->
    fields_refinement R fs.

Hint Constructors succ pred Refinement.
Hint Unfold last.

Inductive fields : id -> [FieldDecl] -> Prop :=
  | F_Obj : fields Object nil
  | F_Decl : forall C S D fs fs'' noDupfs K mds noDupMds fs', 
     find C CT = Some (CDecl C D fs noDupfs K mds noDupMds) ->
     succ (inl C) S ->
     fields_refinement S fs'' ->
     fields D fs' ->
     NoDup (refs (fs' ++ fs ++ fs'')) ->
     fields C (fs'++fs ++ fs'')
  | F_Decl_NoRefine : forall C D fs noDupfs K mds noDupMds fs', 
     find C CT = Some (CDecl C D fs noDupfs K mds noDupMds) ->
     last (inl C) ->
     fields D fs' ->
     NoDup (refs (fs' ++ fs)) ->
     fields C (fs'++fs).
Tactic Notation "fields_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "F_Obj" | Case_aux c "F_Decl"| Case_aux c "F_Decl_NoRefine"].


Reserved Notation "'mtype_r(' m ',' R ')' '=' c '~>' c0" (at level 40, c at next level).
Inductive mtype_refinement (m: id) (R: RefinementName) (Bs: [ClassName]) (B: ClassName): Prop :=
  | mtyr_ok : forall fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines fargs noDupfargs e,
              find_refinement R (CRefine R fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines) ->
              find m mDecls = Some (MDecl B m fargs noDupfargs e) ->
              map fargType fargs = Bs ->
              mtype_r(m, R) = Bs ~> B
  | mtyr_succ: forall S fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines,
              find_refinement R (CRefine R fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines) ->
              find m mDecls = None ->
              succ (inr R) S ->
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
              mtype(m, C) = Bs ~> B
  | mty_no_override: forall S D Fs K Ms noDupfs noDupMds,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
              find m Ms = None ->
              (succ (inl C) S -> forall Bs' B', ~mtype_r(m, S) = Bs' ~> B') ->
              mtype(m, D) = Bs ~> B ->
              mtype(m, C) = Bs ~> B
  | mty_refinement: forall D S Fs K Ms noDupfs noDupMds,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
              find m Ms = None ->
              succ (inl C) S ->
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
  | mbdyr_ok : forall fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines fargs noDupfargs B,
              find_refinement R (CRefine R fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines) ->
              find m mDecls = Some (MDecl B m fargs noDupfargs e) ->
              refs fargs = xs ->
              mbody_r(m, R) = xs o e
  | mbdyr_refine : forall fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines fargs noDupfargs B,
              find_refinement R (CRefine R fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines) ->
              find m mRefines = Some (MRefine B m fargs noDupfargs e) ->
              refs fargs = xs ->
              mbody_r(m, R) = xs o e
  | mbdyr_succ: forall S fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines,
              find_refinement R (CRefine R fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines) ->
              find m mDecls = None ->
              pred R (inr S) ->
              mbody_r(m, S) = xs o e ->
              mbody_r(m, R) = xs o e
  where "'mbody_r(' m ',' R ')' '=' xs 'o' e"
        := (mbody_refinement m R xs e).

Reserved Notation "'mbody(' m ',' D ')' '=' xs 'o' e" (at level 40, xs at next level).
Inductive m_body (m: id) (C: ClassName) (xs: [ClassName]) (e: Exp) : Prop:=
  | mbdy_ok : forall D Fs K Ms noDupfs noDupMds C0 fargs noDupfargs,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
              find m Ms = Some (MDecl C0 m fargs noDupfargs e) ->
              refs fargs = xs ->
              (forall S xs' e', (inl C) <<: S -> ~ mbody_r(m, S) = xs' o e') ->
              mbody(m, C) = xs o e
  | mbdy_no_override: forall D Fs K Ms noDupfs noDupMds,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
              find m Ms = None ->
              (forall S xs' e', (inl C) <<: S -> ~ mbody_r(m, S) = xs' o e') ->
              mbody(m, D) = xs o e ->
              mbody(m, C) = xs o e
  | mbdy_last : forall S,
              (inl C) <<: S -> 
              last (inr S) ->
              mbody_r(m, S) = xs o e ->
              mbody(m, C) = xs o e
  where "'mbody(' m ',' D ')' '=' xs 'o' e" := (m_body m D xs e).

Tactic Notation "mbdy_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "mbdy_ok" | Case_aux c "mbdy_no_override"
  | Case_aux c "mbdy_last" ].

Hint Constructors mbody_refinement m_body.

Inductive override (m: id) (D: ClassName) (Cs: [ClassName]) (C0: ClassName): Prop :=
  | C_override : 
    (forall Ds D0, mtype(m, D) = Ds ~> D0 -> (Ds = Cs /\ C0 = D0)) ->
    override m D Cs C0.

Inductive introduce (m: id) (R: RefinementName): Prop :=
  | I_Refinement : forall S,
    pred R (inr S) ->
    (forall Ds D0, ~ mtype_r(m, S) = Ds ~> D0) ->
    introduce m R
  | I_Class : forall C,
    pred R (inl C) ->
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

Lemma succ_same_ref: forall Cl R,
  succ Cl R ->
  ref Cl = ref R.
Proof.
  destruct 1; crush.
Qed.

Lemma refinement_same_ref : forall R Cl,
  Cl <<: R ->
  ref R = ref Cl.
Proof.
  destruct 1; 
  repeat match goal with
  | H: succ ?C ?R |- _ => apply succ_same_ref in H
  end; crush.
Qed. 
