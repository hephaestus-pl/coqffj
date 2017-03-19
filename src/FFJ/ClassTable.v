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
  | S_Decl: forall C cReference D fs noDupfs K mds noDupMds,
    C = ref cReference ->
    find C CT = Some (CD (CDecl cReference D fs noDupfs K mds noDupMds )) ->
    C <: D
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
  | C_succ : forall C'decl Cs feat feat' n,
    feat = feature C ->
    find_where feat RT = Some n ->
    nth_error RT (S n) = Some feat' ->
    Cs = get_feature feat' CT ->
    find (ref C) Cs = Some C'decl ->
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
     find (ref C) CT = Some (CD (CDecl C D fs noDupfs K mds noDupMds)) ->
    class_declaration C.

Inductive fields : ClassReference -> [FieldDecl] -> Prop :=
 | F_Obj : forall feat, fields (Object @ feat) nil
 | F_Decl : forall C D S fs fsuc noDupfs K mds noDupMds fs',
     find (ref C) CT = Some (CD (CDecl C (ref D) fs noDupfs K mds noDupMds)) ->
     class_declaration D ->
     succ C S ->
     fields S fsuc ->
     fields D fs' ->
     NoDup (refs (fs' ++ fs ++ fsuc)) ->
     fields C (fs' ++ fs ++ fsuc)
  | F_Refine: forall C S fs fsuc noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines,
     find (ref C) CT = Some (CR (CRefine C fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines)) ->
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
     find (ref C) CT = Some (CD (CDecl C (ref D) fs noDupfs K mds noDupMds)) ->
     class_declaration D ->
     succ C S ->
     fields D fs' ->
     NoDup (refs (fs' ++ fs)) ->
     rfields C (fs' ++ fs)
  | RF_Refine: forall C S fs fpred noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines,
     find (ref C) CT = Some (CR (CRefine C fs noDupfDecls K mDecls noDupmDecls mRefines noDupmRefines)) ->
     pred C S ->
     fields S fpred ->
     NoDup (refs (fpred ++ fs)) ->
     rfields C (fpred ++ fs).
Tactic Notation "rfields_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "RF_Obj" | Case_aux c "RF_Decl"
  | Case_aux c "RF_Refine" ].
          

Reserved Notation "'mtype(' m ',' D ')' '=' c '~>' c0" (at level 40, c at next level).
Inductive m_type (m: id) (C: ClassReference) (Bs: [ClassName]) (B: ClassName) : Prop:=
  | mty_ok : forall D Fs K Ms noDupfs noDupMds fargs noDupfargs e,
              find (ref C) CT = Some (CD (CDecl C D Fs noDupfs K Ms noDupMds)) ->
              find m Ms = Some (MDecl B m fargs noDupfargs e) ->
              map fargType fargs = Bs ->
              mtype(m, C) = Bs ~> B
  | mty_no_override: forall D C' Fs K Ms noDupfs noDupMds,
              find (ref C) CT = Some (CD (CDecl C (ref D) Fs noDupfs K Ms noDupMds)) ->
              class_declaration D ->
              find m Ms = None ->
              succ C C' ->
              (exists Bs' B', (mtype(m, C') = Bs' ~> B')) ->
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


Hint Constructors m_type m_body fields.
Tactic Notation "mbdy_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "mbdy_ok" | Case_aux c "mbdy_no_override"].