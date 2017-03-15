Require Import Decidable Relations.
Require Import Base.
Require Import FJ.Syntax.
Require Import FJ.ClassTable.

(* A fixed Refinement Table*)
Parameter RT: [ClassRefinement].

Inductive succ (C: Class) (C': ClassRefinement): Prop :=
  | S_Decl : forall C1 C2 D fs K noDupfs mds noDupMds ft fs' nodupfs' K' mds' noDupMds' mdrs noDupMdrs,
    C = CD (CDecl C1 D fs noDupfs K mds noDupMds) ->
    C' = CRefine C2 ft fs' nodupfs' K' mds' noDupMds' mdrs noDupMdrs ->
    find C1 RT = Some C' ->
    succ C C'
  | S_Refine: forall C1 ft fs nodupfs K mds noDupMds mdrs noDupMdrs C2 ft' fs' nodupfs' K' mds' noDupMds' mdrs' noDupMdrs' n,
    C = CR (CRefine C1 ft fs nodupfs K mds noDupMds mdrs noDupMdrs) ->
    C' = CRefine C2 ft' fs' nodupfs' K' mds' noDupMds' mdrs' noDupMdrs' ->
    find_where C1 (refs RT) = Some n ->
    find C1  (skipn n RT) = Some C' ->
    succ C C'.

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
