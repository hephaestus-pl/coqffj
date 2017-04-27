Require Import List.
Require Import Tactics.
Require Import In.
Import ListNotations.

Definition last_error {A:Type} (l: list A) :=
  head (rev (l)).

Lemma rev_in: forall A l (x:A),
  In x (rev l) ->
  In x l.
Proof.
  intros. induction l; auto.
  simpl in *.
  apply in_app_iff in H; crush.
Qed.

Lemma last_in: forall A l (x:A),
  last_error l = Some x ->
  In x l.
Proof.
  intros.
  unfold last_error in H.
  apply head_In in H. apply rev_in in H.
  assumption.
Qed.