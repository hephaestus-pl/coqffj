Require Import List.
Require Import Tactics.
Import ListNotations.

Definition last_error {A:Type} (l: list A) :=
  head (rev (l)).