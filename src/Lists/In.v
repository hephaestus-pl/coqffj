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

Lemma skipn_In: forall {A: Type} l (x: A) n,
  In x (skipn n l) ->
  In x l.
Proof.
  intros. gen n x.
  induction l; crush. case n in *; crush.
  destruct n; crush.
  specialize IHl with n x; crush.
Qed.

Lemma In_pair_map: forall {A B: Type} (a:A) (b:B) l,
  In (a, b) l -> In b (map snd l).
Proof.
  intros. induction l; crush.
Qed.
