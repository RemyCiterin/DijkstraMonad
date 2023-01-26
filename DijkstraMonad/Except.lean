import DijkstraMonad.Basic
open EffectObservation
open OrderedMonad

universe u v w
#print ExceptT

instance
  {ε : Type u}
  {W:Type u → Type v}
  [Monad W] [OrderedMonad W]
  : OrderedMonad (ExceptT ε W) where

  leW := by
    simp [ExceptT]
    intro α e1 e2
    apply leW e1 e2

  trans := by
    intro α a b c h1 h2
    simp [ExceptT] at a b c
    apply trans a b c h1 h2

  refl := by
    intro α a
    simp [ExceptT] at a
    apply refl a

  bindW := by
    intro α β w w' f f' h1 h2
    simp [ExceptT] at w w' f f'
    simp at h1 h2
    apply bindW <;> try assumption
    simp [ExceptT.bindCont]
    intro x
    cases x <;> simp
    . case a.error x =>
      apply refl
    . case a.ok x =>
      apply h2

#check θ
#check bindθ

theorem fun_apply_same_args {α:Type u} {β:Type v} : (f:α→β) → (x y:α) → x = y → f x = f y := by
  intro f x y h
  induction h
  rfl

instance
  {ε:Type u}
  {M:Type u → Type v}
  {W:Type u → Type w}
  [Monad M] [Monad W]
  [OrderedMonad W]
  [EffectObservation M W]
  : EffectObservation (ExceptT ε M) (ExceptT ε W) where

  θ {α:Type u} (x:ExceptT ε M α) : ExceptT ε W α :=
    @θ M _ _ _ _ _ (Except ε α) x

  bindθ := by
    intro α β m f
    simp [ExceptT] at m f
    simp [bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk]
    simp [bindθ]
    apply fun_apply_same_args
    simp [Function.comp]
    apply funext
    intro x
    cases x
    . simp [pureθ]
    . simp

  pureθ := by
    intro α x
    simp
    apply pureθ


