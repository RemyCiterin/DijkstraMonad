import DijkstraMonad.Read

/-
def StateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (α × σ)
-/

universe u v w

-- define a specification using weakest precondition of StateT from
-- a specification of m
def StateT.wp (σ : Type u) (W:Type u → Type v) (α : Type u) : Type (max u v) := sorry
