universe u v w

#check Trans


-- order relation on monad, allow to define specification monad
class OrderedMonad (W:Type u → Type v) extends Monad W where
  leW : {α:Type u} → W α → W α → Prop
  trans: {α:Type u} → ∀ a b c:W α, leW a b → leW b c → leW a c
  refl : {α:Type u} → ∀ a:W α, leW a a
  bindW :
    {α β: Type u} → (w w':W α) → (f f':α → W β) →
    leW w w' → (∀ x, leW (f x) (f' x)) →
    leW (bind w f) (bind w' f')

#check OrderedMonad.leW

instance {W:Type u → Type w} [OrderedMonad W] {α :Type u} : Trans
  (@OrderedMonad.leW W _ α)
  (@OrderedMonad.leW W _ α)
  (@OrderedMonad.leW W _ α) where
  trans h1 h2 := OrderedMonad.trans _ _ _ h1 h2

notation lhs:80 " ≤ᵂ " rhs:80 => OrderedMonad.leW lhs rhs

-- take W, a specification monad, and return a diskstra, that allow to define and prove programs
-- in the same time
class DijkstraMonad (W : Type u -> Type v) (D:∀ A, W A → Type w) extends OrderedMonad W where
  bindD : {α β:Type u} → {w :W α} → {f:α -> W β} → D α w → (∀ x, D β (f x)) → D β (bind w f)
  pureD : {α:Type u} → (x:α) → D α <| pure x
  compD : {α:Type u} → {w w':W α} → D α w → w ≤ᵂ w' → D α w'

class EffectObservation (M:Type u → Type v) (W:Type u → Type w) [Monad M] [OrderedMonad W] where
  θ : {α:Type u} → M α → W α
  bindθ : {α β: Type u} → (m:M α) → (f:α → M β) → θ (bind m f) = bind (θ m) (Function.comp θ f)
  pureθ : {α: Type u} → (x:α) → θ (pure x) = pure x

instance
  {M:Type u → Type v}
  {W:Type u → Type w}
  [monadM:Monad M]
  [ordMonadW:OrderedMonad W]
  [effectMW:EffectObservation M W] :
  DijkstraMonad W (fun A w => {m:M A // EffectObservation.θ m ≤ᵂ w}) where

  pureD {α: Type u} (x:α) :=
    ⟨pure x, by
      rw [effectMW.pureθ]
      exact ordMonadW.refl (pure x)
    ⟩

  bindD {α β: Type u} {w: W α} {f:α → W β} (m:{m:M α // effectMW.θ m ≤ᵂ w}) (g:∀ x, {m:M β //effectMW.θ m ≤ᵂ f x}) :=
  ⟨
    bind m.val (fun x => (g x).val),
    by
      revert m
      intro ⟨m, hm⟩
      simp
      rw [effectMW.bindθ]
      apply ordMonadW.bindW
      . assumption
      . intro x
        exact (g x).property
  ⟩

  compD {α:Type u} {w w':W α} (m:{m:M α // effectMW.θ m ≤ᵂ w}) (h:w ≤ᵂ w') : {m:M α // effectMW.θ m ≤ᵂ w'} :=
    ⟨
      m.val,
      by
        simp
        apply ordMonadW.trans (effectMW.θ m.val) w w'
        apply m.property
        assumption
    ⟩


