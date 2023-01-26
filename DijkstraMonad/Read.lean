import DijkstraMonad.Basic

universe u v w

/-
def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  ρ → m α
-/

open Monad in
open OrderedMonad in
instance
  {ρ:Type u}
  {W:Type u → Type v}
  [Monad W] [OrderedMonad W]
  : OrderedMonad (ReaderT ρ W) where

  leW {α:Type u} (x y:ReaderT ρ W α) :=
    ∀ r, x r ≤ᵂ y r

  trans := by
    intro α a b c h1 h2 r
    apply OrderedMonad.trans _ (b r) _
    apply h1
    apply h2

  refl := by
    intro α a r
    apply refl

  bindW := by
    intro α β w w' f f' h1 h2 r
    simp [bind, ReaderT.bind]
    apply bindW
    apply h1
    intro x
    apply h2

open Monad in
open OrderedMonad in
open EffectObservation in
instance
  {ρ:Type u}
  {M W:Type u → Type v}
  [Monad W] [OrderedMonad W]
  [Monad M] [EffectObservation M W]
  : EffectObservation (ReaderT ρ M) (ReaderT ρ W) where
  θ {α:Type u} (x:ReaderT ρ M α) := fun r => θ (x r)

  bindθ := by
    intro α β m f
    apply funext
    intro r
    simp [bind, ReaderT.bind]
    apply bindθ

  pureθ := by
    intro α x
    simp [pure, ReaderT.pure]
    apply funext
    intros
    apply pureθ


