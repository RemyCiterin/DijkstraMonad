import DijkstraMonad.Read

/-
def StateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (α × σ)
-/

universe u v w


open Monad in
open OrderedMonad in
open EffectObservation in
instance {σ:Type u}
  {W:Type u → Type v}
  [monadW:Monad W]
  [ordMonadW:OrderedMonad W]
  : OrderedMonad (StateT σ W) where

  leW {α:Type u} (x y:StateT σ W α) := ∀ s, x s ≤ᵂ y s

  trans := by
    intro α a b c h1 h2 s
    apply trans (a s) (b s) (c s)
    apply h1 s
    apply h2 s

  refl := by
    intro α a s
    apply refl

  bindW := by
    intro α β w w' f f' h1 h2 s
    simp [bind, StateT.bind]
    apply bindW
    apply h1
    intro x
    apply h2

open Monad in
open OrderedMonad in
open EffectObservation in
instance {σ:Type u}
  {M W:Type u → Type v}
  [Monad M] [Monad W]
  [OrderedMonad W]
  [EffectObservation M W]
  : EffectObservation (StateT σ M) (StateT σ W) where

  θ {α:Type u} (m:StateT σ M α) : StateT σ W α := fun s => θ (m s)

  bindθ := by
    intro α β m f
    simp [bind, pure, StateT.bind]
    apply funext
    intro x
    apply bindθ

  pureθ := by
    intros α x
    simp [pure, StateT.pure]
    apply funext
    intro s
    apply pureθ

