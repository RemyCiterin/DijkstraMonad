import DijkstraMonad.Basic

#print DijkstraMonad

#print EffectObservation

#print OrderedMonad

universe u

def Id.wp (type:Type u) := {f:(type → Prop) → Prop // ∀ p p':type → Prop, (∀ x, p x → p' x) → f p → f p'}

instance : Monad Id.wp where
  pure {α:Type u} (x:α) := ⟨fun p => p x, by
    intro p p'
    simp
    intro h
    apply h x
  ⟩

  bind {α β: Type u} (m:Id.wp α) (f:α → Id.wp β) : Id.wp β :=
    ⟨
      fun p => m.val (fun a => (f a).val p),
      by
        simp
        intro p p' h1 h2
        apply m.property (fun a => (f a).val p) (fun a => (f a).val p')
        . intro x
          apply (f x).property
          assumption
        . assumption
    ⟩

#check OrderedMonad.bindW

instance : OrderedMonad Id.wp where
  leW {α:Type u} (p1 p2:Id.wp α) := ∀ p, p2.val p → p1.val p

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
    apply h1
    apply h2
    assumption

  bindW {α β:Type u} := by
    simp
    intros w w' f f' h1 h2 p h3
    simp [bind] at *
    apply h1
    apply w'.property (fun a => (f' a).val p) (fun a => (f a).val p)
    . intro x
      apply h2 x p
    . assumption

instance : EffectObservation Id Id.wp where
  θ {α: Type u} (x:α) := pure x

  pureθ := by
    simp

  bindθ := by
    intros α β m f
    simp [bind, pure]

def Id.wp.check {α:Type u} (p:α→Prop) : Id.wp α :=
  ⟨
    fun p' => ∀ x, p x → p' x,
    by
      intros p1 p2 h1 h2 x h3
      apply h1
      apply h2
      assumption
  ⟩

#reduce Id.wp.check (fun x:Nat => x ≤ 2)

def Id.pre_post (α:Type u) := Prop × (α → Prop)

#check Id.pre_post

def Id.pre_post_to_wp {α:Type u} : Id.pre_post α → @Id.wp α :=
  fun (pre, post) => ⟨
    fun p : α → Prop => (pre ∧ (∀ a, post a → p a)),
    by
      intros p p' h
      simp
      intro h'
      constructor
      . exact h'.1
      . intro a h''
        apply h
        apply h'.2
        assumption
  ⟩

#check inferInstanceAs (DijkstraMonad Id.wp (ToDMonad Id Id.wp))
