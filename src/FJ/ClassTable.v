Require Import String.
Require Import Relations Decidable.
Require Import FJ.Base.
Require Import FJ.Syntax.


Reserved Notation "C '<:' D " (at level 40).
Inductive Subtype : id -> ClassName -> Prop :=
  | S_Refl: forall C: ClassName, C <: C
  | S_Trans: forall (C D E: ClassName), 
    C <: D -> 
    D <: E -> 
    C <: E
  | S_Decl: forall C D fs noDupfs K mds noDupMds,
    find C CT = Some (CD (CDecl C D fs noDupfs K mds noDupMds )) ->
    C <: D
where "C '<:' D" := (Subtype C D).
Hint Constructors Subtype.

Tactic Notation "subtype_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "S_Refl" | Case_aux c "S_Trans" 
  | Case_aux c "S_Decl"].

Reserved Notation "C <<: D" (at level 40).
Inductive Succ (C: Class) (C': Class): Prop :=
  | Suc_Decl : forall n,
    find_where (ref C) (refs CT) = Some n ->
    find (ref C) (skipn (S n) CT) = Some C' ->
    C <<: C'
where "C <<: C'" := (Succ C C').

Reserved Notation "'mtype(' m ',' D ')' '=' c '~>' c0" (at level 40, c at next level).
Inductive m_type (m: id) (C: ClassName) (Bs: [ClassName]) (B: ClassName) : Prop:=
  | mty_ok : forall D Fs K Ms noDupfs noDupMds fargs noDupfargs e,
              find C CT = Some (CD (CDecl C D Fs noDupfs K Ms noDupMds)) ->
              find m Ms = Some (MDecl B m fargs noDupfargs e) ->
              map fargType fargs = Bs ->
              mtype(m, C) = Bs ~> B
  | mty_no_override: forall D Fs K Ms noDupfs noDupMds,
              find C CT = Some (CD (CDecl C D Fs noDupfs K Ms noDupMds)) ->
              find m Ms = None ->
              mtype(m, D) = Bs ~> B ->
              mtype(m, C) = Bs ~> B
  where "'mtype(' m ',' D ')' '=' cs '~>' c0"
        := (m_type m D cs c0).

Tactic Notation "mtype_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "mty_ok" | Case_aux c "mty_no_override"].

Inductive m_body (m: id) (C: ClassName) (xs: [ClassName]) (e: Exp) : Prop:=
  | mbdy_ok : forall D Fs K Ms noDupfs noDupMds C0 fargs noDupfargs,
              find C CT = Some (CD (CDecl C D Fs noDupfs K Ms noDupMds)) ->
              find m Ms = Some (MDecl C0 m fargs noDupfargs e) ->
              refs fargs = xs ->
              m_body m C xs e
  | mbdy_no_override: forall D Fs K Ms noDupfs noDupMds,
              find C CT = Some (CD (CDecl C D Fs noDupfs K Ms noDupMds)) ->
              find m Ms = None ->
              m_body m D xs e ->
              m_body m C xs e.
Notation "'mbody(' m ',' D ')' '=' xs 'o' e" := (m_body m D xs e) (at level 40).

Inductive fields : id -> [FieldDecl] -> Prop :=
 | F_Obj : fields Object nil
 | F_Decl : forall C D fs  noDupfs K mds noDupMds fs', 
     find C CT = Some (CD (CDecl C D fs noDupfs K mds noDupMds)) ->
     fields D fs' ->
     NoDup (refs (fs' ++ fs)) ->
     fields C (fs'++fs).
Tactic Notation "fields_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "F_Obj" | Case_aux c "F_Decl"].

Hint Constructors m_type m_body fields.
Tactic Notation "mbdy_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "mbdy_ok" | Case_aux c "mbdy_no_override"].


Fixpoint suc (C: ClassName) ft ct : option ClassRefinement :=
  match ct with
  | nil => None
  | c :: cs => 
   match c with 
    | CD _ => suc C ft cs
    | CR ((CRefine C' ft' _ _ _ _ _ _ _) as CRef) => 
     match beq_id C C' with
      | true => if lt_dec ft ft' then Some CRef else suc C ft cs
      | false => suc C ft cs
     end
   end
  end.
