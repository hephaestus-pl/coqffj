Require Import String.
Require Import Relations Decidable.
Require Import FFJ.Base.
Require Import FFJ.Syntax.
Require Import FFJ.ClassTable.

Fixpoint subst (e: Exp) (ds: [Exp]) (xs: [Var]): Exp := 
  match e with
  | ExpVar var => match find_where var xs with
                  | Some i => match nth_error ds i with
                                   | None => e | Some di => di end
                  | None => e end
  | ExpFieldAccess exp i => ExpFieldAccess (subst exp ds xs) i
  | ExpMethodInvoc exp i exps => 
      ExpMethodInvoc (subst exp ds xs) i (map (fun x => subst x ds xs) exps)
  | ExpCast cname exp => ExpCast cname (subst exp ds xs)
  | ExpNew cname exps => ExpNew cname (map (fun x => subst x ds xs) exps)
  end.
Notation " [; ds '\' xs ;] e " := (subst e ds xs) (at level 30).


Inductive Warning (s: string) : Prop :=
  | w_str : Warning s.
Notation stupid_warning := (Warning "stupid warning").

(* We can make a stupid cast at anytime, but that rule must be flagged. *)
Axiom STUPID_STEP : stupid_warning.

Reserved Notation "Gamma '|--' x ':' C" (at level 60, x at next level).
Inductive ExpTyping (Gamma: env ClassName) : Exp -> ClassName -> Prop :=
  | T_Var : forall x C, get Gamma x = Some C -> 
                Gamma |-- ExpVar x : C
  | T_Field: forall e0 C0 fs i Fi Ci fi,
                Gamma |-- e0 : C0 ->
                fields C0 fs ->
                nth_error fs i = Some Fi ->
                Ci = fieldType Fi ->
                fi = ref Fi ->
                Gamma |-- ExpFieldAccess e0 fi : Ci
  | T_Invk : forall e0 C Cs C0 Ds m es,
                Gamma |-- e0 : C0 ->
                mtype(m, C0) = Ds ~> C ->
                Forall2 (ExpTyping Gamma) es Cs ->
                Forall2 Subtype Cs Ds ->
                Gamma |-- ExpMethodInvoc e0 m es : C
  | T_New : forall C Ds Cs fs es,
                fields C fs ->
                Ds = map fieldType fs ->
                Forall2 (ExpTyping Gamma) es Cs ->
                Forall2 Subtype Cs Ds ->
                Gamma |-- ExpNew C es : C
  | T_UCast : forall e0 D C,
                Gamma |-- e0 : D ->
                D <: C ->
                Gamma |-- ExpCast C e0 : C
  | T_DCast : forall e0 C D,
                Gamma |-- e0 : D ->
                C <: D ->
                C <> D ->
                Gamma |-- ExpCast C e0 : C
  | T_SCast : forall e0 D C,
                Gamma |-- e0 : D ->
                ~ D <: C ->
                ~ C <: D ->
                stupid_warning ->
                Gamma |-- ExpCast C e0 : C
  where " Gamma '|--' e ':' C " := (ExpTyping Gamma e C).

Tactic Notation "typing_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Field" 
  | Case_aux c "T_Invk" | Case_aux c "T_New"
  | Case_aux c "T_UCast" | Case_aux c "T_DCast" 
  | Case_aux c "T_SCast"].

Reserved Notation "e '~>!' e1" (at level 59).
Inductive Computation_step : Exp -> Exp -> Prop :=
  | R_Field : forall C Fs es fi ei i,
            fields C Fs ->
            nth_error Fs i = Some fi ->
            nth_error es i = Some ei-> 
            ExpFieldAccess (ExpNew C es) (ref fi) ~>! ei
  | R_Invk : forall C m xs ds es e0,
            mbody(m, C) = xs o e0 ->
            NoDup (this :: xs) ->
            List.length ds = List.length xs ->
            ExpMethodInvoc (ExpNew C es) m ds ~>! [; ExpNew C es :: ds \ this :: xs;] e0
  | R_Cast : forall C D es,
            C <: D ->
            ExpCast D (ExpNew C es) ~>! ExpNew C es
  where "e '~>!' e1" := (Computation_step e e1).
Tactic Notation "computation_step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "R_Field" | Case_aux c "R_Invk" 
  | Case_aux c "R_Cast" ].

Reserved Notation "e '~>' e1" (at level 60).
Inductive Computation : Exp -> Exp -> Prop :=
  | R_Step : forall e e1, e ~>! e1 -> e ~> e1
  | RC_Field : forall e0 e0' f,
            e0 ~> e0' ->
            ExpFieldAccess e0 f ~> ExpFieldAccess e0' f
  | RC_Invk_Recv : forall e0 e0' m es,
            e0 ~> e0' ->
            ExpMethodInvoc e0 m es ~> ExpMethodInvoc e0' m es
  | RC_Invk_Arg : forall e0 ei' m es es' ei i,
            ei ~> ei' ->
            nth_error es i = Some ei ->
            nth_error es' i = Some ei' ->
            (forall j, j <> i -> nth_error es j = nth_error es' j) ->
            length es = length es' ->
            ExpMethodInvoc e0 m es ~> ExpMethodInvoc e0 m es'
  | RC_New_Arg : forall C ei' es es' ei i,
            ei ~> ei' ->
            nth_error es i = Some ei ->
            nth_error es' i = Some ei' ->
            (forall j, j <> i -> nth_error es j = nth_error es' j) ->
            length es = length es' ->
            ExpNew C es ~> ExpNew C es'
  | RC_Cast : forall C e0 e0',
            e0 ~> e0' ->
            ExpCast C e0 ~> ExpCast C e0'
  where "e '~>' e1" := (Computation e e1).

Tactic Notation "computation_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "R_Step" | Case_aux c "RC_Field"
  | Case_aux c "RC_Invk_Recv" | Case_aux c "RC_Invk_Arg" 
  | Case_aux c "RC_New_Arg" | Case_aux c "RC_Cast"].

Inductive Value : Exp -> Prop :=
  v_new: forall C es, Value (ExpNew C es).


Reserved Notation "e '~>*' e1" (at level 59).
Inductive ComputationStar : Exp -> Exp -> Prop := 
  | Comp_Refl : forall e,
    e ~>* e
  | Comp_Trans: forall e1 e2 e3,
    e1 ~>* e2 ->
    e2 ~>* e3 ->
    e1 ~>* e2
  where "e '~>*' e1" := (ComputationStar e e1).
Hint Constructors Computation ExpTyping Value ComputationStar.
Definition normal_form {X:Type} (R: relation X) (t: X) :=
  ~exists t', R t t'.


Definition override (m: id) (D: ClassName) (Cs: [ClassName]) (C0: ClassName) :=
    (forall Ds D0, mtype(m, D) = Ds ~> D0 -> (Ds = Cs /\ C0 = D0)).

(* We cut off introduce in this rule, because our definition of introduce only checks backwards,
  hence no need to check on a Class Declaration *)
Inductive MType_OK : ClassName -> MethodDecl -> Prop :=
  | T_Method : forall C D C0 E0 xs Cs e0 Fs noDupfs K Ms noDupMds fargs m noDupFargs,
            nil extds (this :: xs) : (C :: Cs) |-- e0 : E0 ->
            E0 <: C0 ->
            find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
            override m D Cs C0 ->
            map fargType fargs = Cs ->
            refs fargs = xs ->
            find m Ms = Some (MDecl C0 m fargs noDupFargs e0) ->
            MType_OK C (MDecl C0 m fargs noDupFargs e0).

(*In the paper there is no override in this rule, but if you don't need it here
then you wouldn't need it in MType_OK also *)
Inductive MType_CRefinement_OK : RefinementName -> MethodDecl -> Prop :=
  | TCR_Method : forall R C D C0 E0 xs Cs e0 feat fs noDupfDecls K Ms noDupmDecls mRefines noDupmRefines m fargs noDupFargs fs' noDupfDecls' K' Ms' noDupMds',
            nil extds (this :: xs) : (C :: Cs) |-- e0 : E0 ->
            E0 <: C0 ->
            R = C @ feat ->
            find C CT = Some (CDecl C D fs' noDupfDecls' K' Ms' noDupMds') ->
            find_refinement R (CRefine R fs noDupfDecls K Ms noDupmDecls mRefines noDupmRefines) ->
            override m D Cs C0 ->
            map fargType fargs = Cs ->
            refs fargs = xs ->
            find m Ms = Some (MDecl C0 m fargs noDupFargs e0) ->
            introduce m R ->
            MType_CRefinement_OK R (MDecl C0 m fargs noDupFargs e0).

Inductive MRType_OK: RefinementName -> MethodRefinement -> Prop :=
  | TR_Method : forall R C C0 E0 xs Cs e0 feat fs noDupfDecls K Ms noDupmDecls mRefines noDupmRefines m fargs noDupFargs,
            nil extds (this :: xs) : (C :: Cs) |-- e0 : E0 ->
            E0 <: C0 ->
            R = C @ feat ->
            find_refinement R (CRefine R fs noDupfDecls K Ms noDupmDecls mRefines noDupmRefines) ->
            map fargType fargs = Cs ->
            refs fargs = xs ->
            find m mRefines = Some (MRefine C0 m fargs noDupFargs e0) ->
            find m Ms = None ->
            extend m R Cs C0 ->
            MRType_OK R (MRefine C0 m fargs noDupFargs e0).

Inductive CType_OK: ClassDecl -> Prop :=
  | T_Class : forall C D Fs noDupfs K Ms noDupMds Cfargs Dfargs fdecl,
            K = KDecl C (Cfargs ++ Dfargs) (map Arg (refs Cfargs)) (zipWith Assgnmt (map (ExpFieldAccess (ExpVar this)) (refs Fs)) (map ExpVar (refs Fs))) ->
            fields D fdecl ->
            NoDup (refs (fdecl ++ Fs)) ->
            Forall (MType_OK C) (Ms) ->
            find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
            CType_OK (CDecl C D Fs noDupfs K Ms noDupMds).

Inductive CRType_OK: ClassRefinement -> Prop :=
    | TR_Class : forall R P feat C Fs noDupfs K Ms noDupMds fdecl mRefines noDupmRefines,
            R = C @ feat ->
            C <> Object ->
            find_refinement R (CRefine R Fs noDupfs K Ms noDupMds mRefines noDupmRefines) ->
            pred R P ->
            rfields P fdecl ->
            NoDup (refs (fdecl ++ Fs)) ->
            Forall (MType_OK C) (Ms) ->
            Forall (MRType_OK R) (mRefines) ->
            CRType_OK (CRefine R Fs noDupfs K Ms noDupMds mRefines noDupmRefines).

(* Hypothesis for ClassTable sanity *)
Module CTSanity.

Hypothesis obj_notin_dom: find Object CT = None.
Hint Rewrite obj_notin_dom.

Hypothesis dec_subtype: forall C D,
  decidable (Subtype C D).

Hypothesis antisym_subtype:
  antisymmetric _ Subtype.


Hypothesis superClass_in_dom: forall C D Fs noDupfs K Ms noDupMds,
  find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
  D <> Object ->
  exists D0 Fs0 noDupfs0 K0 Ms0 noDupMds0, find D CT = Some (CDecl D D0 Fs0 noDupfs0 K0 Ms0 noDupMds0).

Hypothesis RT_wellformed:
  Forall (fun CR => CRType_OK CR) RT.

Lemma succ_in_dom: forall Cl S,
  succ Cl S ->
  exists CD, find_refinement S CD.
Proof.
  induction 1.
  assert (forall R, In R RT -> CRType_OK R). apply Forall_forall.
  exact RT_wellformed.
  specialize H2 with CR. destruct H2.
  unfold refinements_of in H0.
  apply head_In in H0. 
 SearchAbout filter. apply filter_In in H0. crush. 
  assert (S = R). crush. subst.
eexists; crush. eauto.
  subst. 
  subst.  
 lets _: RT_wellformed. apply Forall_forall in RT_wellformed.

Hypothesis ClassesOK: forall C CD, 
  find C CT = Some CD->
  CType_OK CD.
Hint Resolve ClassesOK.

Hypothesis ClassesRefinementOK: forall R RD, 
  find_refinement R RD ->
  CRType_OK RD.
Hint Resolve ClassesOK.

Lemma subtype_obj_obj: forall C,
  Object <: C ->
  Object = C.
Proof.
  intros_all. remember Object as Obj.
  induction H; crush.
Qed.

Lemma sub_not_obj: forall C,
  Object <> C ->
  ~ Object <: C.
Proof.
  Hint Resolve subtype_obj_obj.
  intros_all. remember Object as Obj.
  induction H; crush.
Qed.


End CTSanity.

Definition ExpTyping_ind' := 
  fun (Gamma : env ClassName) (P : Exp -> ClassName -> Prop)
  (f : forall (x : id) (C : ClassName), get Gamma x = Some C -> P (ExpVar x) C)
  (f0 : forall (e0 : Exp) (C0 : ClassName) (fs : [FieldDecl]) (i : nat) (Fi : FieldDecl)
          (Ci : ClassName) (fi : id),
        Gamma |-- e0 : C0 ->
        P e0 C0 ->
        fields C0 fs ->
        nth_error fs i = Some Fi -> Ci = fieldType Fi -> fi = ref Fi -> P (ExpFieldAccess e0 fi) Ci)
  (f1 : forall (e0 : Exp) (C : ClassName) (Cs : [ClassName]) (C0 : ClassName) (Ds : [ClassName]) 
          (m : id) (es : [Exp]),
        Gamma |-- e0 : C0 ->
        P e0 C0 ->
        mtype( m, C0)= Ds ~> C ->
        Forall2 (ExpTyping Gamma) es Cs ->
        Forall2 Subtype Cs Ds -> 
        Forall2 P es Cs ->
        P (ExpMethodInvoc e0 m es) C)
  (f2 : forall (C : id) (Ds Cs : [ClassName]) (fs : [FieldDecl]) (es : [Exp]),
        fields C fs ->
        Ds = map fieldType fs ->
        Forall2 (ExpTyping Gamma) es Cs ->
        Forall2 Subtype Cs Ds -> 
        Forall2 P es Cs ->
        P (ExpNew C es) C)
  (f3 : forall (e0 : Exp) (D C : ClassName), Gamma |-- e0 : D -> P e0 D -> D <: C -> P (ExpCast C e0) C)
  (f4 : forall (e0 : Exp) (C : id) (D : ClassName),
        Gamma |-- e0 : D -> P e0 D -> C <: D -> C <> D -> P (ExpCast C e0) C)
  (f5 : forall (e0 : Exp) (D C : ClassName),
        Gamma |-- e0 : D -> P e0 D -> ~ D <: C -> ~ C <: D -> stupid_warning -> P (ExpCast C e0) C) =>
fix F (e : Exp) (c : ClassName) (e0 : Gamma |-- e : c) {struct e0} : P e c :=
  match e0 in (_ |-- e1 : c0) return (P e1 c0) with
  | T_Var _ x C e1 => f x C e1
  | T_Field _ e1 C0 fs i Fi Ci fi e2 f6 e3 e4 e5 => f0 e1 C0 fs i Fi Ci fi e2 (F e1 C0 e2) f6 e3 e4 e5
  | T_Invk _ e1 C Cs C0 Ds m es e2 m0 f6 f7 => f1 e1 C Cs C0 Ds m es e2 (F e1 C0 e2) m0 f6 f7 
          ((fix list_Forall_ind (es' : [Exp]) (Cs' : [ClassName]) 
            (map : Forall2 (ExpTyping Gamma) es' Cs'): 
               Forall2 P es' Cs' :=
            match map with
            | Forall2_nil _ => Forall2_nil P
            | (@Forall2_cons _ _ _ ex cx ees ccs H1 H2) => Forall2_cons ex cx (F ex cx H1) (list_Forall_ind ees ccs H2)
          end) es Cs f6)
  | T_New _ C Ds Cs fs es f6 e1 f7 f8 => f2 C Ds Cs fs es f6 e1 f7 f8
          ((fix list_Forall_ind (es' : [Exp]) (Cs' : [ClassName]) 
            (map : Forall2 (ExpTyping Gamma) es' Cs'): 
               Forall2 P es' Cs' :=
            match map with
            | Forall2_nil _ => Forall2_nil P
            | (@Forall2_cons _ _ _ ex cx ees ccs H1 H2) => Forall2_cons ex cx (F ex cx H1) (list_Forall_ind ees ccs H2)
          end) es Cs f7)
  | T_UCast _ e1 D C e2 s => f3 e1 D C e2 (F e1 D e2) s
  | T_DCast _ e1 C D e2 s n => f4 e1 C D e2 (F e1 D e2) s n
  | T_SCast _ e1 D C e2 s s0 w => f5 e1 D C e2 (F e1 D e2) s s0 w
  end.