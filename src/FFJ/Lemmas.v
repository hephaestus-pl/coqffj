Require Import Relation_Definitions.
Require Import FFJ.Base.
Require Import FFJ.Syntax.
Require Import FFJ.ClassTable.
Require Import FFJ.Semantics.

Include FFJ.Semantics.CTSanity.

(* General Use Tactics *)


Ltac class_OK C:=
  match goal with
    | [ H: find C ?CT = Some _ |- _ ] => 
      apply ClassesOK in H; inversion H; subst; sort; clear H
  end.

Ltac insterU H :=
  repeat match type of H with
           | forall x : ?T, _ =>
             let x := fresh "x" in
               evar (x : T);
               let x' := eval unfold x in x in
                 clear x; specialize (H x')
         end.

Ltac find_dec_with T Ref L i :=
  destruct (@find_dec T) with Ref L i.

Ltac find_dec_tac L i:=
  match type of L with
  | list ?T => let H := fresh "H" in destruct (find_dec L i) as [H|H]
  end.

Ltac decompose_ex H :=
  repeat match type of H with
           | ex (fun x => _) =>
             let x := fresh x in
             destruct H as [x H]; sort
         end.

Ltac decompose_exs :=
  repeat match goal with
  | [H: exists x, _ |- _ ] => decompose_ex H
  end.

Ltac inv_decl :=
  repeat let C := fresh "C" in
  let feat := fresh "feat" in
  let R := fresh "R" in
  let D := fresh "D" in
  let K := fresh "K" in
  let Kr := fresh "Kr" in
  let m := fresh "m" in
  let f := fresh "f" in
  let fargs := fresh "fargs" in
  let noDupFargs := fresh "noDupFargs" in
  let noDupfs := fresh "noDupfs" in
  let fs := fresh "fs" in
  let Ms := fresh "Ms" in
  let noDupMs := fresh "noDupMs" in
  let Mrs := fresh "Mrs" in
  let noDupMrs := fresh "noDupMrs" in
  match goal with
  | [ MD : MethodDecl |- _ ] => destruct MD as [C m fargs noDupFargs e]
  | [ FD : FieldDecl |- _ ] => destruct FD as [C f]
  | [ CD : ClassDecl |- _ ] => destruct CD as [C D fs noDupfs K Ms noDupMs]
  | [ CR : ClassRefinement |- _ ] => destruct CR as [R fs noDupfs Kr Ms noDupMs Mrs noDupMrs]
  | [ R : RefinementName |- _ ] => destruct R as [C feat]
  end.

Ltac Forall_find_tac :=
  let H := fresh "H" in
  match goal with
  | [ H1: Forall ?P ?l, H2: find ?x ?l = _ |- _ ] => lets H: H1; eapply Forall_find in H; [|eexact H2]; clear H1
  end.

Ltac mtypes_ok :=
  match goal with
  | [H: MType_OK _ _ |- _ ] => destruct H; subst; sort; clear H
  end.

Ltac elim_eqs :=
  repeat match goal with
  | [H: ?x = _, H1: ?x = _ |- _ ] => rewrite H in H1; inversion H1; clear H1; subst
  end.

Ltac unify_override :=
  match goal with
  | [H: override ?m ?D ?Cs ?C0, H1: mtype(?m, ?D) = ?Ds ~> ?D0 |- _ ] => destruct H with Ds D0; [exact H1 | subst; clear H]
  end.

(* Auxiliary Lemmas *)
(* mtype / MType_OK lemmas *)
Lemma unify_returnType' : forall Ds D C D0 Fs noDupfs K Ms noDupMds C0 m fargs noDupfargs ret,
  mtype( m, C)= Ds ~> D ->
  find C CT = Some (CDecl C D0 Fs noDupfs K Ms noDupMds) ->
  find m Ms = Some (MDecl C0 m fargs noDupfargs ret) ->
  D = C0.
Proof.
  induction 1; crush.
Qed.


Lemma unify_fargsType : forall Ds D C D0 Fs noDupfs K Ms noDupMds C0 m fargs noDupfargs ret,
  mtype( m, C)= Ds ~> D ->
  find C CT = Some (CDecl C D0 Fs noDupfs K Ms noDupMds) ->
  find m Ms = Some (MDecl C0 m fargs noDupfargs ret) ->
  Ds = map fargType fargs.
Proof.
  induction 1; crush.
Qed.

Lemma methodDecl_OK :forall C D0 Fs noDupfs K Ms noDupMds C0 m fargs noDupfargs ret,
  find m Ms = Some (MDecl C0 m fargs noDupfargs ret) ->
  find C CT = Some (CDecl C D0 Fs noDupfs K Ms noDupMds) ->
  MType_OK C (MDecl C0 m fargs noDupfargs ret).
Proof.
  intros. apply ClassesOK in H0; inversion H0.
  match goal with
  [ H: Forall _ _ |- _ ] =>  eapply Forall_find in H; eauto
  end.
Qed.
Hint Resolve methodDecl_OK.
(*
Lemma mbody_in_succ : forall C D Fs noDupfs K Ms noDupMds m MD,
  find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
  find m Ms = Some MD ->
  (forall S xs' e', succ (inl C) S -> ~mbody_r(m, S) = xs' o e').
Proof.
Admitted.
*)
Lemma mbodyr_mtyper: forall m R xs e,
  mbody_r(m, R) = xs o e ->
  exists Bs B, mtype_r(m, R) = Bs ~> B.
Proof.
Admitted.

Lemma exists_mbody_r: forall C D Cs m,
  mtype_r(m, C) = Cs ~> D ->
  exists xs e, mbody_r(m, C) = xs o e /\ NoDup (this :: xs) /\ length Cs = length xs.
Proof.
  induction 1.
  - exists (refs fargs) e. repeat (split; crush; eauto).
  - decompose_exs. exists xs e. repeat (split; crush; eauto).
Qed.

Lemma exists_mbody: forall C D Cs m,
  mtype(m, C) = Cs ~> D ->
  exists xs e, mbody(m, C) = xs o e /\ NoDup (this :: xs) /\ length Cs = length xs.
Proof.
  induction 1; eauto.
  - exists (refs fargs) e; repeat (split; eauto); crush.
    eapply mbody_ok; eauto. intros_all. 
    eapply mbodyr_mtyper in H3. destruct H3. decompose_exs. eauto.
  - crush; eexists; eauto. eexists. split. eapply mbody_no_override; eauto.
    intros_all. eapply mbodyr_mtyper in H7. decompose_exs; eauto.
    split; eauto.
  - edestruct exists_mbody_r; eauto. crush.
    do 2 eexists. split. eapply mbody_last; crush; eauto. eauto.
Qed.

(* find C CT Lemmas *)

Lemma mtype_obj_False: forall m Cs C,
  mtype(m, Object) = Cs ~> C ->
  False.
Proof.
  inversion 1; crush.
Qed.
Hint Resolve mtype_obj_False.

Lemma super_obj_or_defined: forall C D Fs noDupfs K Ms noDupMds,
    find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
    D = Object \/ exists D0 Fs0 noDupfs0 K0 Ms0 noDupMds0, 
                    find D CT = Some (CDecl D D0 Fs0 noDupfs0 K0 Ms0 noDupMds0).
Proof.
  intros. destruct beq_id_dec with D Object; subst.
  left; auto.
  right. eapply superClass_in_dom; eauto.
Qed.


(* fields Lemmas *)
Lemma fields_obj_nil: forall f,
  fields Object f -> f = nil.
Proof.
  remember Object.
  induction 1; crush.
Qed.

Lemma fields_NoDup : forall C fs,
  fields C fs ->
  NoDup (refs fs).
Proof.
  inversion 1; crush.
Qed.

(* Unification Tactics *)


Ltac mtype_OK m :=
  match goal with
    | [ H: find ?C _ = Some (CDecl _ _ _ _ _ ?Ms _ ), H1: find m ?Ms = Some (MDecl _ _ _ _ _) |- _ ] => 
      eapply methodDecl_OK in H1; eauto; inversion H1; subst; sort; clear H1
  end.

Ltac unify_returnType :=  match goal with
  | [H: mtype( ?m, ?C)= ?Ds ~> ?D,
     H1: find ?C _ = Some (CDecl ?C _ _ _ _ ?Ms _),
     H2: find ?m ?Ms = Some (MDecl ?D ?m _ _ _) |- _ ] => fail 1 (*needed for no infinite loop *)
  | [H: mtype( ?m, ?C)= ?Ds ~> ?D,
     H1: find ?C _ = Some (CDecl ?C _ _ _ _ ?Ms _),
     H2: find ?m ?Ms = Some (MDecl ?C0 ?m _ _ _) |- _ ] => lets ?H: unify_returnType' H H1 H2; subst
  end.

Ltac unify_fargsType :=  match goal with
  | [H: mtype( ?m, ?C)= map fargType ?fargs ~> ?D,
     H1: find ?C _ = Some (CDecl ?C _ _ _ _ ?Ms _),
     H2: find ?m ?Ms = Some (MDecl _ ?m ?fargs _ _) |- _ ] => fail 1
  | [H: mtype( ?m, ?C)= ?Ds ~> ?D,
     H1: find ?C _ = Some (CDecl ?C _ _ _ _ ?Ms _),
     H2: find ?m ?Ms = Some (MDecl _ ?m ?fargs _ _) |- _ ] => lets ?H: unify_fargsType H H1 H2; subst
  end.

Ltac superclass_defined_or_obj C :=
  match goal with
  | [H1: find C _ = _ |- _ ] => edestruct super_obj_or_defined; [eexact H1 |  | ]; subst
  end.


Ltac unify_find_ref :=
  repeat let H := fresh "H" in
  match goal with
  | [H1: find ?x ?xs = Some ?u |- _] => assert (ref u = x) as H; [eapply find_ref_inv; eauto|]; subst;
    repeat match goal with
      | [ H2 : context[ref u] |- _] => simpl in H2
    end; simpl
  end.

(**)

(*
Ltac solve_last_succ :=
  match goal with
  | [H: last ?R, H1: succ ?R ?S |- _ ] => false; unfold last in H; specialize H with S; apply H in H1; exact H1
  end.
*)


Lemma pred_det: forall R R' S,
  pred S R ->
  pred S R' ->
  R = R'.
Proof.
  intros. gen R'.
  induction H.
  intros.
  inversion H2.
  inv_decl. unify_find_ref. subst. simpl in *. inversion H7; subst; clear H7.
  elim_eqs; reflexivity.
Qed.

Lemma find_refinement_det: forall R RD1 RD2,
  find_refinement R RD1 ->
  find_refinement R RD2 ->
  RD1 = RD2.
Proof.
  intros. gen RD2.
  induction H. subst.
  intros. inversion H0. inversion H; subst.
  rewrite H3 in H1; crush.
Qed.

Lemma find_refinement_same_name: forall R R' fs noDupfs Kr Ms noDupMs Mrs noDupMrs,
  find_refinement R (CRefine R' fs noDupfs Kr Ms noDupMs Mrs noDupMrs) ->
  find_refinement R (CRefine R fs noDupfs Kr Ms noDupMs Mrs noDupMrs).
Proof.
  intros. lets ?H: H. apply find_refinement_same_refinement in H.
  destruct R. destruct R'. crush.
Qed.

Ltac unify_pred :=
  match goal with
  | [H: pred ?R ?S1, H1: pred ?R ?S2 |- _ ] => assert (S1 = S2) by (apply pred_det with R; [exact H| exact H1]); clear H1; subst
  end.

Ltac unify_find_refinement :=
  match goal with
  | [H: find_refinement ?R ?RD1, H1: find_refinement ?R ?RD2 |- _ ] => assert (RD1 = RD2) by (eapply find_refinement_det with R; [eexact H| eexact H1]); clear H1; subst
  end.

Ltac unify_find_refinement' :=
  match goal with
  | [H: find_refinement ?R (CRefine ?R' _ _ _ _ _ _ _) |- _ ] => apply find_refinement_same_name in H
  end.

Ltac solve_first_pred :=
  match goal with
  | [H: pred ?R ?S, H1: first_refinement ?R |- _ ] => unfold first_refinement in H1; specialize H1 with S; contradiction
  end.

Lemma fields_refinement_det: forall R f1 f2,
  fields_refinement R f1 ->
  fields_refinement R f2 ->
  f1 = f2.
Proof.
  intros. gen f1.
  induction H0.
  - intros. inversion H3. simpl in *; subst. unify_pred. unify_find_refinement.
    specialize IHfields_refinement with fpred0; crush.
    subst. solve_first_pred. 
  - intros_all. inversion H1. solve_first_pred. subst. unify_find_refinement; crush.
Qed.


Ltac unify_fields_refinement :=
  match goal with
  | [H: fields_refinement ?R ?f1, H1: fields_refinement ?R ?f2 |- _ ] => destruct (fields_refinement_det _ _ _ H H1); clear H1; subst
  end.


Lemma fields_det: forall C f1 f2,
  fields C f1 ->
  fields C f2 ->
  f1 = f2.
Proof.
  Hint Resolve fields_obj_nil fields_refinement_det.
  intros; gen f1.
  fields_cases (induction H0) Case; intros.
  Case "F_Obj".
    crush.
  Case "F_Decl".
    destruct H4.
    rewrite obj_notin_dom in H; crush.
    simpl in *; subst. elim_eqs.
    apply IHfields in H7. subst. unify_fields_refinement. reflexivity.
    elim_eqs.
    inversion H3. subst. crush. subst.
    elim_eqs.
    subst. elim_eqs. apply IHfields in H6; subst; eauto.
Qed.


Ltac unify_fields :=
  match goal with
  | [ H1: fields ?C ?f1, H2: fields ?C ?f2 |- _ ] => destruct (fields_det _ _ _ H1 H2); subst; clear H2
  end.

Ltac unifall :=
  repeat (decompose_exs || inv_decl || unify_find_ref || elim_eqs
  || unify_find_ref || unify_override || unify_fields || unify_fields_refinement 
  || unify_find_refinement' || unify_find_refinement
  || unify_returnType || unify_fargsType
  || mtypes_ok  || Forall_find_tac).

Ltac ecrush := unifall; eauto; crush; eauto.

Lemma methods_same_signature: forall C D Fs noDupfs K Ms noDupMds Ds D0 m,
    find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
    mtype(m, D) = Ds ~> D0 ->
    mtype(m, C) = Ds ~> D0.
Proof.
  intros; class_OK C.
  find_dec_tac Ms m. 
  ecrush; eapply mty_ok; ecrush.
  eapply mty_no_override; ecrush.
Admitted.

(* Subtype Lemmas *)

Lemma obj_not_subtype: forall C,
  C <> Object -> ~ Object <: C.
Proof.
  intros; intro. 
  remember Object. induction H0; [auto | | crush].
  subst. destruct beq_id_dec with D Object; subst; auto.
Qed.

Lemma pred_dec: forall R,
  {exists S, pred R S} + {first_refinement R}.
Proof.
  assert (forall A f (l: [A]), {x:A | f l = Some x} + {f l = None}).
  intros. destruct (f l); ecrush.
  destruct R as [C feat].
  lets ?H: X (find_where feat) (refs (refinements_of C)).
  destruct H. destruct s as [n]. destruct n.
  right. unfold first_refinement. intros_all. inversion H. destruct CR. destruct r. subst. simpl in *.
  elim_eqs.
  destruct X with (f:= fun (l: [ClassRefinement]) => nth_error l n) (l:= refinements_of C).
  destruct s as [CR]. left. exists (class_name CR @ ref CR); eauto.
  right. intros_all. inversion H; ecrush.
  right; intros_all. inversion H; ecrush.
Qed.


Lemma last_refinement_fields: forall C CR CD,
  find C CT = Some CD ->
  last_refinement C = Some CR ->
  exists fs, fields_refinement CR fs.
Proof.
  intros. lets ?H: H0.
  class_OK C. apply last_refinement_in_dom in H0. destruct H0 as [CRD].
  destruct CRD. destruct CR.  unifall. 
  apply ClassesRefinementOK in H. 
  inversion H; eexists; solve [econstructor; eauto].
Qed.

Lemma subtype_fields: forall C D fs ,
  C <: D ->
  fields D fs ->
  exists fs', fields C (fs ++ fs').
Proof.
  Hint Rewrite app_nil_r app_assoc.
  intros. gen H0. gen fs.
  subtype_cases (induction H) Case; intros.
  Case "S_Refl".
    exists (@nil FieldDecl); crush.
  Case "S_Trans".
    repeat match goal with
    | [H: forall fs, fields ?C fs -> _, H1: fields ?C ?fs|- _ ] => destruct (H fs H1); clear H
    end; ecrush.
  Case "S_Decl".
    assert (forall A f, {x:A | f = Some x} + {f = None}).
    intros. destruct f; ecrush.
    destruct X with (f:= last_refinement C). destruct s as [CR].
    lets ?H: H. lets ?H: e.
    eapply last_refinement_fields in H; eauto. destruct H as [fs'].
    apply last_refinement_in_dom in H2. destruct H2 as [CRD].
    class_OK C; solve [eexists; econstructor; ecrush].
    class_OK C; solve [eexists; econstructor; ecrush].
Qed.

Lemma subtype_order:
  order _ Subtype.
Proof.
  refine {| ord_refl:= (S_Refl); ord_trans:= (S_Trans); ord_antisym:=antisym_subtype|}.
Qed.

Lemma super_class_subtype: forall C D D0 fs noDupfs K mds noDupMds,
 C <: D -> C <> D ->
 find C CT = Some (CDecl C D0 fs noDupfs K mds noDupMds) ->
 D0 <: D.
Proof.
  intros C D D0 fs noDupfs K mds noDupMds H.
  gen D0 fs noDupfs K mds noDupMds.
  induction H; [crush | intros | crush].
  destruct beq_id_dec with C D; ecrush.
Qed.

Lemma subtype_not_sub': forall C D E,
  E <: C ->
  E <: D ->
  C <: D \/ D <: C.
Proof.
  Hint Resolve super_class_subtype.
  intros C D E H. gen D.
  induction H; auto; intros. 
  - edestruct IHSubtype1; eauto.
  - destruct beq_id_dec with C D0; ecrush.
Qed.

Lemma subtype_not_sub: forall C D E,
    E <: D ->
  ~ C <: D ->
  ~ D <: C ->
  ~ E <: C.
Proof.
  intros_all.
  match goal with
  | [H: ?E <: ?D, H1: ?E <: ?C |- _ ] => edestruct subtype_not_sub' with (D:=D); eauto
  end.
Qed.

(* subst Lemmas *)
Lemma var_subst_in: forall ds xs x i di,
  nth_error xs i = Some x ->
  nth_error ds i = Some di ->
  NoDup xs ->
  [; ds \ xs ;] (ExpVar x) = di.
Proof.
  Hint Rewrite nth_error_nil.
  intros. gen ds xs i.
  induction ds, xs; crush.
  apply findwhere_ntherror in H; crush.
Qed.

(* Paper Lemmas *)

Lemma A11: forall m D C Cs C0,
          C <: D ->
          mtype(m,D) = Cs ~> C0 ->
          mtype(m,C) = Cs ~> C0.
Proof.
  Hint Resolve methods_same_signature.
  induction 1; eauto.
Qed.


Lemma weakening: forall Gamma e C,
  nil |-- e : C ->
  Gamma |-- e : C.
Proof.
  induction 1 using ExpTyping_ind'; eauto; crush.
Qed.



Lemma A14: forall D m C0 xs Ds e,
  mtype(m,C0) = Ds ~> D ->
  mbody(m,C0) = xs o e ->
  exists D0 C,  C0 <: D0 /\ C <: D /\
  nil extds (this :: xs) : (D0 :: Ds) |-- e : C.
Proof.
  intros.
  mbdy_cases (induction H0) Case.
  mtype_OK m. exists C E0. unifall; eauto.
  Case "mbdy_no_override".
    inversion H; ecrush.
    exists x x0; ecrush.
Admitted.


Theorem term_subst_preserv_typing : forall Gamma xs (Bs: list ClassName) D ds As e,
  nil extds xs : Bs |-- e : D ->
  NoDup xs ->
  Forall2 (ExpTyping Gamma) ds As ->
  Forall2 Subtype As Bs ->
  length ds = length xs ->
  exists C, (C <:D /\ Gamma |-- [; ds \ xs ;] e : C).
Proof with eauto.
  intros.
  typing_cases (induction H using ExpTyping_ind') Case; sort.
  Case "T_Var".
    destruct (In_dec (beq_id_dec) x xs) as [xIn|xNIn]; unifall; eauto.
    SCase "In x xs". rename C into Bi.
      assert (In x xs); eauto.
      apply nth_error_In' in xIn as [i]. symmetry in H3.
      edestruct (@nth_error_same_len id Exp) as [di]...
      assert (nth_error Bs i = Some Bi).
      eapply get_noDup_extds; eauto; constructor; eauto. 
      destruct (Forall2_nth_error _ _ (ExpTyping Gamma) ds As i di) as [Ai]...
      exists Ai.
      split.
      eapply Forall2_forall... erewrite var_subst_in; eauto.
      eapply Forall2_forall...
    SCase "~In x xs". 
      split with C. split. eauto.
      erewrite notin_extds in H... inversion H. 
  Case "T_Field".
    simpl. destruct IHExpTyping as [C']. destruct H8. 
    exists Ci. 
    split...
    eapply subtype_fields in H8... destruct H8 as [fs'].
    eapply T_Field. eassumption.  eapply H8. eapply nth_error_app_app... auto. auto.
  Case "T_Invk". rename C0 into D0.
    destruct IHExpTyping as [C0]. destruct H8.
    apply A11 with (m:=m) (Cs:=Ds) (C0:=C) in H8...
    exists C. split; auto. simpl. 
    apply Forall2_exi in H7. destruct H7 as [Cs']. sort. destruct H7.
    apply Forall2_trans with (zs:= Ds) in H7; auto.
    eapply T_Invk; eauto.
    apply Forall2_map; auto.
    intros x y z ?H ?H1; apply S_Trans with y; auto. 
  Case "T_New".
    apply Forall2_exi in H7. destruct H7 as [Cs']. destruct H7; sort.
    exists C; split; auto. simpl. 
    apply Forall2_trans with (zs:= Ds) in H7; auto.
    eapply T_New...
    apply Forall2_map; auto.
    intros x y z ?H ?H1; apply S_Trans with y; auto.
  Case "T_UCast".
    exists C. split; auto. simpl.
    destruct IHExpTyping as [E]. destruct H5.
    eapply T_UCast...
  Case "T_DCast".
    exists C; split; auto. simpl.
    destruct IHExpTyping as [E]. destruct H6.
    destruct dec_subtype with E C.
    eapply T_UCast in H7...
    destruct beq_id_dec with E C. rewrite e in H8; false; apply H8; auto.
    destruct dec_subtype with C E.
    eapply T_DCast in H7...
    eapply T_SCast in H7...
    apply STUPID_STEP.
  Case "T_SCast".
    exists C; split; auto. simpl.
    destruct IHExpTyping as [E]. destruct H7.
    eapply T_SCast...
    eapply subtype_not_sub...
Qed. 


Lemma exists_subtyping : forall Gamma es es' Cs Ds i ei ei' C D C0,
  nth_error es i = Some ei ->
  nth_error es' i = Some ei' ->
  nth_error Cs i = Some C ->
  nth_error Ds i = Some D ->
  Forall2 Subtype Cs Ds ->
  C0 <: C ->
  Gamma |-- ei' : C0 ->
  Forall2 (ExpTyping Gamma) es Cs ->
  (forall j, j <> i -> nth_error es j = nth_error es' j) ->
  exists Cs', Forall2 Subtype Cs' Ds /\
             Forall2 (ExpTyping Gamma) es' Cs'.
Proof.
  intros. 
  exists (firstn i Cs ++ cons C0 nil ++ skipn (S i) Cs).
  gen i ei' H H0 H1 H2 H3 H5. gen es' Ds. induction H6 as [| ?e ?C ?es ?Cs].
  intros. crush.
  intros. 
  destruct es' as [| es']; [rewrite nth_error_nil in H1; inversion H1|].
  destruct Ds as [| Ds]; [rewrite nth_error_nil in H3; inversion H3|].
  destruct i. simpl in *. crush. inversion H5; constructor; auto. subst. apply S_Trans with C; auto.
  constructor; auto.
  assert (forall i, nth_error es i = nth_error es'0 i). intro.
  lets ?H: H7 (S i). 
 simpl in H0. apply H0; intuition.
  apply nth_error_same with (xs' := es'0) in H0. rewrite <- H0; auto. 
  edestruct IHForall2 with (es':= es'0); eauto; intros.
  lets ?H: H7 (S j); crush. inversion H5; auto.
  clear IHForall2.
  split. crush. constructor; auto. inversion H5; auto.
  crush. constructor; auto.
  lets ?H: H7 0. simpl in H11. assert (e = es'); crush.
Qed.

