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
  match type of H with
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
  match type of H with
           | ex (fun x => _) =>
             let x := fresh x in
             destruct H as [x H]; sort
         end.

Ltac decompose_exs :=
  match goal with
  | [H: exists x, _ |- _ ] => decompose_ex H
  end.

Ltac inv_decl :=
  match goal with
  | [ MD : MethodDecl |- _ ] => destruct MD as [?C ?m ?fargs ?noDupFargs ?e]
  | [ FD : FieldDecl |- _ ] => destruct FD as [?C ?f]
  | [ CD : ClassDecl |- _ ] => destruct CD as [?C ?D ?fs ?noDupfs ?K ?Ms ?noDupMs]
  | [ CR : ClassRefinement |- _ ] => destruct CR as [?R ?fs ?noDupfs ?Kr ?Ms ?noDupMs ?Mrs ?noDupMrs]
  | [ R : RefinementName |- _ ] => destruct R as [?C ?feat]
  end.

Ltac Forall_find_tac :=
  let H := fresh "H" in
  match goal with
  | [ H1: Forall ?P ?l, H2: find ?x ?l = _ |- _ ] => lets H: H1; eapply Forall_find in H; [|eexact H2]; clear H1
  end.

Ltac mtypes_ok :=
  match goal with
  | [H: MType_OK _ _ |- _ ] => destruct H; subst; sort; clear H
  | [H: MRType_OK _ _ |- _ ] => destruct H; subst; sort; clear H
  end.

Ltac elim_eqs :=
  match goal with
  | [H: ?x = _, H1: ?x = _ |- _ ] => rewrite H in H1; inversion H1; clear H1; subst
  end.

Ltac inv_refname :=
  match goal with
  | [H: ?C @ ?feat = ?D @ ?feat' |- _ ] => inversion H; subst; clear H
  end.

Ltac inv_crefine:=
  match goal with
  | [H: CRefine _ _ _ _ _ _ _ _ = CRefine _ _ _ _ _ _ _ _ |- _ ] => inversion H; subst; clear H
  end.


Ltac unify_override :=
  match goal with
  | [H: override ?m ?D ?Cs ?C0, H1: mtype(?m, ?D) = ?Ds ~> ?D0 |- _ ] => destruct H with Ds D0; [exact H1 | subst; clear H]
  end.

Ltac pred_same_name :=
  match goal with
  | [H: pred ?R ?S |- _ ] => assert (class_name R = class_name S) by (apply (pred_same_cname _ _ H))
  end.

Ltac unify_find_ref :=
  let H := fresh "H" in
  match goal with
  | [H1: find ?x ?xs = Some ?u |- _] => assert (ref u = x) as H; [eapply find_ref_inv; eauto|]; subst;
    match goal with
      | [ H2 : context[ref u] |- _] => simpl in H2
    end; simpl
  end.

Lemma opt_fun_dec: forall A (l: [A]) (f: [A] -> option A), 
  {exists (x:A), f l = Some x} + {f l = None}.
Proof. crush. destruct f as [|a]; crush. left; exists a; auto.
Qed.

Lemma last_error_refinement: forall C R,
  last_refinement C = Some R ->
  exists CR, last_error (refinements_of C) = Some CR /\ (class_name CR @ ref CR = R).
Proof.
  intros. unfold last_refinement in *.
  destruct opt_fun_dec with ClassRefinement (refinements_of C) (last_error: [ClassRefinement] -> option ClassRefinement).
  decompose_exs; rewrite e in H. exists x; crush.
  rewrite e in H. inversion H.
Qed.

Lemma last_refinement_same_name: forall C R, 
  last_refinement C = Some R ->
  class_name R = C.
Proof.
  intros. apply last_error_refinement in H. decompose_exs. destruct H.
  SearchAbout last_error.
  apply last_in in H.
  lets ?H: refinements_same_name C.
  rewrite Forall_forall in H1. eapply H1 in H.
  crush.
Qed.

Ltac lastref_samename :=
  match goal with
  |[H: last_refinement ?C = Some (?C @ _) |- _ ] => fail 1
  |[H: last_refinement ?C = Some (?C1 @ _) |- _ ] => 
    lets ?H: H; apply last_refinement_same_name in H; simpl in *; subst
  end.

Hint Resolve last_refinement_same_name.

Lemma last_refinement_in: forall C R, 
  last_refinement C = Some R ->
  exists CR, In CR RT /\ class_name CR = C /\ ref CR = ref R.
Proof.
  intros. unfold last_refinement in H.
  destruct opt_fun_dec with ClassRefinement (refinements_of C) (last_error: [ClassRefinement] -> option ClassRefinement).
  decompose_exs.
  rewrite e in H.
  apply last_in in e.
  unfold refinements_of in e.
  apply filter_In in e. exists x; crush. destruct x. destruct r.
  apply beq_id_eq in H1. auto.
  rewrite e in H; crush.
Qed.

Lemma last_find: forall (A: Set) l (x: A) `{Referable A},
  last_error l = Some x ->
  exists x', find (ref x) l = Some x'.
Proof.
  intros. apply last_in in H0. induction l. crush.
  destruct H0. subst; eexists; eauto. simpl. crush.
  crush. destruct beq_id_dec with (ref x) (ref a).
  eexists; crush.
  exists x0. rewrite not_eq_beq_id_false; eauto. 
Qed.

(*
Lemma last_refinement_find: forall C R,
  last_refinement C = Some R ->
  exists CR, find_refinement R CR.
Proof.
  Print find_refinement.
  intros.
  apply last_error_refinement in H. decompose_exs. destruct H.
   lets ?H: refinements_same_name C.
  rewrite Forall_forall in H1. eapply last_find in H. decompose_exs.
  lets ?H: H. apply find_ref_inv in H.
  apply find_in in H2. apply H1 in H2. subst.

(* preciso que as feats sejam unicas *)
Admitted.
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
  repeat inv_decl. repeat unify_find_ref. subst. simpl in *. inversion H7; subst; clear H7.
  repeat elim_eqs; reflexivity.
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
  R = R'.
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
  | [H: find_refinement ?R ?RD1, H1: find_refinement ?R ?RD2 |- _ ] => apply (find_refinement_det _ _ _ H) in H1; inversion H1; clear H1; subst
  end.

Ltac unify_find_refinement' :=
  match goal with
  | [H: find_refinement ?R (CRefine ?R _ _ _ _ _ _ _) |- _ ] => fail 1
  | [H: find_refinement ?R (CRefine ?R' _ _ _ _ _ _ _) |- _ ] => destruct (find_refinement_same_name _ _ _ _ _ _ _ _ _ H)
  end.

Ltac solve_first_pred :=
  match goal with
  | [H: pred ?R ?S, H1: first_refinement ?R |- _ ] => unfold first_refinement in H1; specialize H1 with S; contradiction
  end.


Lemma mnotin_last_notmtyper : forall R m,
  mnotin_refinement m R ->
  forall Ds D, ~mtype_r(m, R) = Ds ~> D.
Proof.
  intros_all. gen Ds D.
  induction H; let X:=fresh "H" in intros Ds D X; induction X;unify_find_refinement; crush.
  destruct H2 with S; crush.
  unify_pred. eapply IHmnotin_refinement; eauto.
Qed.

Ltac notin_mtyper :=
  match goal with
  |[H: mnotin_refinement ?m ?R,
    H1: mtype_r(?m, ?R) = ?Ds ~> ?D |- _ ] => 
    false; apply (mnotin_last_notmtyper _ _ H H1) with Ds D
  |[H: last_refinement ?C = Some ?S,
    H1: mnotin_last_refinement ?m ?C,
    H2: mtype_r(?m, ?S) = ?Ds ~> ?D |- _ ] => 
    false; apply H1 in H; apply mnotin_last_notmtyper with S m Ds D in H; contradiction
  end.

(* Auxiliary Lemmas *)
(* mtype / MType_OK lemmas *)
Lemma unify_returnType' : forall Ds D C D0 Fs noDupfs K Ms noDupMds C0 m fargs noDupfargs ret,
  mtype( m, C)= Ds ~> D ->
  find C CT = Some (CDecl C D0 Fs noDupfs K Ms noDupMds) ->
  find m Ms = Some (MDecl C0 m fargs noDupfargs ret) ->
  mnotin_last_refinement m C ->
  D = C0.
Proof.
  induction 1; crush. 
  - notin_mtyper.
Qed.


Lemma unify_fargsType : forall Ds D C D0 Fs noDupfs K Ms noDupMds C0 m fargs noDupfargs ret,
  mtype( m, C)= Ds ~> D ->
  find C CT = Some (CDecl C D0 Fs noDupfs K Ms noDupMds) ->
  find m Ms = Some (MDecl C0 m fargs noDupfargs ret) ->
  mnotin_last_refinement m C ->
  Ds = map fargType fargs.
Proof.
  induction 1; crush.
  - notin_mtyper. 
Qed.


Lemma mbodyr_mtyper: forall m R xs e,
  mbody_r(m, R) = xs o e ->
  exists Bs B, mtype_r(m, R) = Bs ~> B.
Proof.
  induction 1; repeat decompose_exs; do 2 eexists; eauto.
Qed.

Lemma exists_mbody_r: forall C D Cs m,
  mtype_r(m, C) = Cs ~> D ->
  exists xs e, mbody_r(m, C) = xs o e /\ NoDup (this :: xs) /\ length Cs = length xs.
Proof.
  induction 1.
  - exists (refs fargs) e. repeat (split; crush; eauto).
  - repeat decompose_exs. exists (refs fargs) e. repeat (split; crush; eauto).
  - repeat decompose_exs. exists xs e. repeat (split; crush; eauto).
Qed.

Lemma exists_mbody: forall C D Cs m,
  mtype(m, C) = Cs ~> D ->
  exists xs e, mbody(m, C) = xs o e /\ NoDup (this :: xs) /\ length Cs = length xs.
Proof.
  induction 1; eauto.
  - exists (refs fargs) e; repeat (split; eauto); crush.
  - crush; eexists; eauto.
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

Ltac unify_returnType :=  match goal with
  | [H: mtype( ?m, ?C)= ?Ds ~> ?D,
     H1: find ?C _ = Some (CDecl ?C _ _ _ _ ?Ms _),
     H2: find ?m ?Ms = Some (MDecl ?D ?m _ _ _),
     H3: mnotin_last_refinement ?m ?C |- _ ] => fail 1 (*needed for no infinite loop *)
  | [H: mtype( ?m, ?C)= ?Ds ~> ?D,
     H1: find ?C _ = Some (CDecl ?C _ _ _ _ ?Ms _),
     H2: find ?m ?Ms = Some (MDecl ?C0 ?m _ _ _),
     H3: mnotin_last_refinement ?m ?C |- _ ] => lets ?H: unify_returnType' H H1 H2 H3; subst
  end.

Ltac unify_fargsType :=  match goal with
  | [H: mtype( ?m, ?C)= map fargType ?fargs ~> ?D,
     H1: find ?C _ = Some (CDecl ?C _ _ _ _ ?Ms _),
     H2: find ?m ?Ms = Some (MDecl _ ?m ?fargs _ _) |- _ ] => fail 1
  | [H: mtype( ?m, ?C)= ?Ds ~> ?D,
     H1: find ?C _ = Some (CDecl ?C _ _ _ _ ?Ms _),
     H2: find ?m ?Ms = Some (MDecl _ ?m ?fargs _ _),
     H3:  mnotin_last_refinement ?m ?C |- _ ] => lets ?H: unify_fargsType H H1 H2 H3; subst
  end.

Ltac superclass_defined_or_obj C :=
  match goal with
  | [H1: find C _ = _ |- _ ] => edestruct super_obj_or_defined; [eexact H1 |  | ]; subst
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
  - intros_all. inversion H1. solve_first_pred. subst.  unify_find_refinement; crush.
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
    simpl in *; subst. repeat elim_eqs.
    apply IHfields in H7. subst. unify_fields_refinement. reflexivity.
    elim_eqs.
    inversion H3. subst. crush. subst.
    repeat elim_eqs.
    subst. repeat elim_eqs. apply IHfields in H6; subst; eauto.
Qed.


Ltac unify_fields :=
  match goal with
  | [ H1: fields ?C ?f1, H2: fields ?C ?f2 |- _ ] => destruct (fields_det _ _ _ H1 H2); subst; clear H2
  end.

Ltac unifall :=
  repeat (decompose_exs || inv_decl || elim_eqs || inv_refname || inv_crefine
  || unify_find_ref || unify_override || unify_fields || unify_fields_refinement 
  || unify_find_refinement' || unify_find_refinement
  || unify_returnType || unify_fargsType || unify_pred
  || lastref_samename
  || mtypes_ok  || Forall_find_tac).



Ltac ecrush := unifall; eauto; crush; eauto.
(* Methods OK Lemmas *)


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

Lemma methodDecl_OK' :forall R D0 Fs noDupfs K Ms noDupMds Mrs noDupMrs C0 m fargs noDupfargs ret,
  find m Ms = Some (MDecl C0 m fargs noDupfargs ret) ->
  find_refinement R (CRefine D0 Fs noDupfs K Ms noDupMds Mrs noDupMrs) ->
  MType_CRefinement_OK R (MDecl C0 m fargs noDupfargs ret).
Proof.
  intros. unifall. apply ClassesRefinementOK in H0; inversion H0;
  match goal with
  [ H: Forall _ _ |- _ ] => solve [eapply Forall_find in H; eauto]
  end.
Qed.

Lemma methodRefinement_OK :forall R D0 Fs noDupfs K Ms noDupMds Mrs noDupMrs C0 m fargs noDupfargs ret,
  find m Mrs = Some (MRefine C0 m fargs noDupfargs ret) ->
  find_refinement R (CRefine D0 Fs noDupfs K Ms noDupMds Mrs noDupMrs) ->
  MRType_OK R (MRefine C0 m fargs noDupfargs ret).
Proof.
  intros. unifall. apply ClassesRefinementOK in H0; inversion H0;
  match goal with
  [ H: Forall _ _ |- _ ] => solve [eapply Forall_find in H; eauto]
  end.
Qed.


Ltac mtype_OK m :=
  match goal with
  | [ H: find ?C _ = Some (CDecl _ _ _ _ _ ?Ms _ ), H1: find m ?Ms = Some (MDecl _ _ _ _ _) |- _ ] => 
      eapply methodDecl_OK in H1; eauto; inversion H1; subst; sort; clear H1
  | [ H: find_refinement ?R (CRefine _ _ _ _ ?Ms _ _ _), H1: find m ?Ms = Some (MDecl _ _ _ _ _) |- _ ] => 
      eapply methodDecl_OK' in H1; eauto; inversion H1; subst; sort; clear H1
  | [ H: find_refinement ?R (CRefine _ _ _ _ _ _ ?Mrs _), H1: find m ?Mrs = Some (MRefine _ _ _ _ _) |- _ ] => 
      eapply methodRefinement_OK in H1; eauto; inversion H1; subst; sort; clear H1
  end.

Ltac last_OK R :=
  match goal with
  | [ H: last_refinement ?C = Some R |- _ ] => 
    lets ?H: H; apply last_refinement_in in H; decompose_exs; destruct H as (H & ?H & ?H);
    apply ClassesRefinementOK' in H; inversion H; clear H; simpl in *; unifall; sort
  end.


Lemma last_refinement_dec:forall C,
  {exists R, last_refinement C = Some R} + {last_refinement C = None}.
Proof. 
  intros.
  destruct (last_refinement C); crush. left; eexists; eauto.
Qed.

Lemma mrefine_dec: forall m R,
  (exists Ds D0, mtype_r(m, R) = Ds ~> D0) \/ mnotin_refinement m R.
Proof.
Admitted.

Lemma mtyper_super_mtype: forall R Ds D0 Ds' D0' C D Fs noDupfs K Ms noDupMds m,
  find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
  last_refinement C = Some R ->
  mtype(m, D) = Ds ~> D0 ->
  mtype_r(m, R) = Ds' ~> D0' ->
  Ds = Ds' /\ D0 = D0'.
Admitted.

Lemma methods_same_signature': forall C R m Ds D0 D Fs noDupfs K Ms noDupMds,
  find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
  last_refinement C = Some R ->
  mtype_r(m, R) = Ds ~> D0 ->
  mtype(m, C) = Ds ~> D0.
Proof.
  intros; class_OK C; unifall.
  induction H1.
Admitted.

Lemma methods_same_signature: forall C D Fs noDupfs K Ms noDupMds Ds D0 m,
    find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
    mtype(m, D) = Ds ~> D0 ->
    mtype(m, C) = Ds ~> D0.
Proof.
  intros; class_OK C.
  destruct last_refinement_dec with C. unifall.
  - destruct mrefine_dec with m (C @ feat). unifall.
    * eapply methods_same_signature'; eauto.
      edestruct mtyper_super_mtype; ecrush.
    * find_dec_tac Ms m; unifall.
      + ecrush; eapply mty_ok; ecrush.
      + eapply mty_no_override; ecrush.
  - find_dec_tac Ms m; unifall.
    * ecrush; eapply mty_ok; ecrush.
    * eapply mty_no_override; ecrush.
Qed.

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
  intros. inv_decl.
  class_OK C.
  last_OK CR;
  solve [eexists; econstructor; eauto].
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
    last_OK CR.
    class_OK C; solve [eexists; econstructor; ecrush].
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

Lemma A14': forall feat D m C0 xs Ds e,
  mtype_r(m,(C0 @ feat)) = Ds ~> D ->
  mbody_r(m,(C0 @ feat)) = xs o e ->
  exists D0 C,  C0 <: D0 /\ C <: D /\
  nil extds (this :: xs) : (D0 :: Ds) |-- e : C.
Proof.
  intros. assert (class_name (C0 @ feat) = C0) by crush.
  mbdy_r_cases (induction H0) Case; subst.
  Case "mbodyr_ok". 
    mtype_OK m. unifall. inversion H; ecrush.
  Case "mbodyr_refine".
    inversion H; ecrush. sort. mtype_OK m; unifall. simpl in H7.
    do 2 eexists; ecrush.
  Case "mbodyr_pred".
    inversion H; pred_same_name; ecrush.
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
    inversion H; ecrush; sort.
    exists x x0; ecrush. 
    notin_mtyper.
  Case "mbdy_last".
    inversion H; ecrush; sort.
    - apply mbodyr_mtyper in H2. unifall. notin_mtyper.
    - apply mbodyr_mtyper in H2. unifall. notin_mtyper.
    - eapply A14'; ecrush.
Qed.


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

