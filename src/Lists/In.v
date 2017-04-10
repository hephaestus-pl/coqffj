Require Import List.
Require Import FFJ.Tactics.

Lemma in_notin_noteq: forall {A:Type} xs (x1: A) x2,
  In x1 xs ->
  ~In x2 xs ->
  x1 <> x2.
Proof.
  induction xs.
  intros; inversion H.
  intros.
  simpl in *.
  apply Decidable.not_or in H0. destruct H0.
  destruct H.
  rewrite <- H; auto.
  apply IHxs; auto.
Qed.

Lemma head_In: forall {A: Type} l (x: A),
  head l = Some x ->
  In x l.
Proof.
  intros x l.
  induction l; crush.
Qed. 
