import DijkstraMonad.State
import DijkstraMonad.Notations
import DijkstraMonad.Except
open DijkstraMonad
open EffectObservation
open OrderedMonad
universe u v w


structure HeapCell where
  α : Type 0
  data : α

structure Heap where
  n : Nat
  f : Fin n → Option HeapCell


def Heap.alloc {α:Type 0} (x:α) (h:Heap) : Heap :=
  ⟨.succ h.n, fun ⟨i, _⟩ => dite (i<h.n) (fun p => h.f ⟨i, p⟩) (fun _ => .some <| HeapCell.mk α x)⟩

def Heap.free (h:Heap) (i:Fin h.n) : Heap :=
  ⟨h.n, fun ⟨j, p⟩ => dite (i = j) (fun _ => h.f ⟨j, p⟩) (fun _ => .none)⟩

def Heap.free_if_exists (heap:Heap) (i:Nat) :=
  dite (i < heap.n) (fun h => Heap.free heap ⟨i, h⟩) (fun _ => heap)


def MemM.alloc {α:Type 0} (x:α) :
  ToDMonad (StateT Heap Id) (StateT Heap Id.wp) PUnit (fun s => Id.wp.check (fun (_, s') => s' = Heap.alloc x s)) :=
  Do {
    with get >>= fun h => set (Heap.alloc x h) using (by
      simp [leW]
      intro s p h1
      simp [Id.wp.check] at h1
      simpStateT
      apply h1
      simp
    );
    let heap ← toDMonad _ _ get with θ get using (by
      simp [leW]
      intro s p
      simp [θ, pure]
      intro h
      simpStateT
      assumption
    );
    toDMonad _ _ <| set (Heap.alloc x heap) with θ <| set (Heap.alloc x heap) using (by
      simp [leW, θ]
      simpStateT
      intro _ p h1
      assumption
    )
  }

#reduce StateT Heap Id.wp PUnit
#check θ
def MemM.free (i:Nat) :
  ToDMonad (StateT Heap Id) (StateT Heap Id.wp) PUnit (fun s =>
  ⟨fun p => i<s.n ∧ ∀ (h:i<s.n), p (PUnit.unit, Heap.free s ⟨i, h⟩), by
    intro p p' h1 h2
    constructor
    . apply h2.1
    . intro h
      apply h1
      apply h2.2
  ⟩) := Do {

    with get >>= fun s => set (Heap.free_if_exists s i) using (by
      simp [leW]
      simpStateT
      intro s p h1
      simp [Heap.free_if_exists]
      apply @Classical.byCases (i < s.n)
      <;> intro h2 <;> simp [h2]
      . apply h1.2
      . apply False.elim
        exact h2 h1.1
    );
    let heap ← toDMonad _ _ get with θ get using (by
      simp [leW, θ]
      simpStateT
      intro s p h
      assumption
    );
    toDMonad _ _ <| set (Heap.free_if_exists heap i)
      with θ <| set (Heap.free_if_exists heap i)
      using (by
      simp [leW, θ]
      simpStateT
      intro s p h
      assumption
    )
  }
