import DijkstraMonad.Id

universe u v w

/-
def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  ρ → m α
-/

-- define a readerT specification from a specification of m
def ReaderT.wp (ρ:Type u) (W:Type u → Type v) (α:Type u) : Type (max u v) := sorry
