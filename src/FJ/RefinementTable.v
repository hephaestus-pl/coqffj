Require Import Decidable Relations.
Require Import Base.
Require Import FJ.Syntax.
Require Import FJ.ClassTable.

(* A fixed Refinement Table*)
Parameter RT: ClassRefinement -> RefinementName.

Definition isRefinement (C: Class): bool:=
  match C with
  | CD _ => false
  | CR _ => true
  end.

Definition RefT := filter isRefinement CT.


Inductive succ (C: Class) (C': ClassRefinement): Prop :=
  | S_Decl : forall C1 C2 D fs K noDupfs mds noDupMds ft fs' nodupfs' K' mds' noDupMds',
    C = CD (CDecl C1 D fs noDupfs K mds noDupMds ) ->
    C' = (CRefine C2 ft fs' nodupfs' K' mds' noDupMds') ->
    find (ref C) RefT = Some (CR (CRefine C2 ft fs' nodupfs' K' mds' noDupMds')) ->
    succ C C'.

Fixpoint suc (C: ClassName) ft ct : option ClassRefinement :=
  match ct with
  | nil => None
  | c :: cs => 
   match c with 
    | CD _ => suc C ft cs
    | CR ((CRefine C' ft' _ _ _ _ _) as CRef) => 
     match beq_id C C' with
      | true => if lt_dec ft ft' then Some CRef else suc C ft cs
      | false => suc C ft cs
     end
   end
  end.

Definition succ (C: Class) : option ClassRefinement :=
  match C with
  | CD CDec => suc (ref CDec) 0 CT
  | CR (CRefi