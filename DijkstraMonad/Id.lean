import DijkstraMonad.Basic

#print DijkstraMonad

#print EffectObservation

#print OrderedMonad

universe u

def Id.wp (type:Type u) := (type → Prop) → Prop

instance : Monad Id.wp where
  pure {α:Type u} (x:α) := fun p => p x

  bind {α β: Type u} (m:Id.wp α) (f:α → Id.wp β) : Id.wp β :=
    fun p => m (fun a => f a p)

instance : OrderedMonad Id.wp where
  leW {α:Type u} (p1 p2:Id.wp α) := ∀ p, p1 p → p2 p

  refl {α:Type u} (p:Id.wp α) := by
    simp
    intro p'
    intros
    assumption

  trans {α:Type u} (a b c:Id.wp α) := by
    simp
    intro h1 h2
    intro p
    intros
    apply h2
    apply h1
    assumption

  bindW

