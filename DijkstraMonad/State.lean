import DijkstraMonad.Read

/-
def StateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (α × σ)
-/

universe u v w

-- define a specification using weakest precondition of StateT from
-- a specification of m
def StateT.wp (σ : Type u) (W:Type u → Type v) (α : Type u) : Type (max u v) :=
  {f:(σ × α → Prop) → σ → Prop // ∀ p p' s, (∀ x, p x → p' x) → f p s → f p' s} × W α

#print StateT.wp

instance {W:Type u → Type v} {σ:Type u}
  [Monad W]
  [OrderedMonad W]
  : Monad (StateT.wp σ W) where

  pure {α:Type u} (x:α) : StateT.wp σ W α := (⟨
    fun p s0 => p (s0, x),
    by
      intro p p' s h
      simp
      apply h
    ⟩, pure x)

  bind {α β:Type u} (m:StateT.wp σ W α) (f:α → StateT.wp σ W β) : StateT.wp σ W β :=
    (⟨
      fun p s0 => m.1.val (fun (s1, x) => (f x).1.val p s1) s0,
      by
        simp
        intro p p' s h1 h2
        apply m.1.property (fun x => (f x.2).1.val p x.1) (fun x => (f x.2).1.val p' x.1)
        . intro x
          apply (f x.2).1.2
          assumption
        . assumption
    ⟩, bind m.2 $ fun x => (f x).2)

#check OrderedMonad.refl
#check OrderedMonad.trans


instance {W:Type u → Type v} {σ:Type u}
  [monadW:Monad W]
  [oMonadW:OrderedMonad W]
  : OrderedMonad (StateT.wp σ W) where

  leW {α:Type u} (p1 p2:StateT.wp σ W α) : Prop := (∀ p s, p2.1.1 p s → p1.1.1 p s) ∧ p1.2 ≤ᵂ p2.2

  refl {α:Type u} (p:StateT.wp σ W α) := by
    constructor
    . intros p' s h
      assumption
    . apply oMonadW.refl

  trans {α:Type u} a b c := by
    intro h1 h2
    constructor
    . intros
      apply h1.1
      apply h2.1
      assumption
    . apply oMonadW.trans _ _ _ h1.2 h2.2

  bindW := by
    intro α β w w' f f' h1 h2
    constructor
    sorry
