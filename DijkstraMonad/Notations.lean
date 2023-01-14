import DijkstraMonad.State

open EffectObservation
open OrderedMonad
open DijkstraMonad


#check inferInstanceAs (DijkstraMonad Id.wp (ToDMonad Id Id.wp))

declare_syntax_cat dijkstra_do
declare_syntax_cat dijkstra_singleton

syntax term " with " term " using " term : dijkstra_singleton
syntax term : dijkstra_singleton

syntax "let" ident " <- " dijkstra_singleton " ; " dijkstra_do : dijkstra_do
syntax "let" ident " ← " dijkstra_singleton " ; " dijkstra_do : dijkstra_do
syntax "let" ident " := " term " ; " dijkstra_do : dijkstra_do
syntax "with" term " using " term " ; " dijkstra_do : dijkstra_do
syntax dijkstra_singleton : dijkstra_do
syntax dijkstra_singleton " ; " dijkstra_do : dijkstra_do

syntax "Do { " dijkstra_do " } " : term
syntax "DoSing { " dijkstra_singleton " } " : term

#check compD

#check fun i:Nat => i

macro_rules
| `(DoSing { $t:term }) =>
  `($t)
| `(DoSing { $t1:term with $t2:term using $t3:term }) =>
  `(@DijkstraMonad.compD _ _ _ _ _ _ $t2 _ $t1 $t3)

macro_rules
| `(Do { let $id:ident ← $t1:dijkstra_singleton ; $dd:dijkstra_do }) =>
  `(DijkstraMonad.bindD (DoSing { $t1 }) fun $id => Do { $dd })

| `(Do { let $id:ident <- $t1:dijkstra_singleton ; $dd:dijkstra_do }) =>
  `(Do { let $id ← $t1 ; $dd })

| `(Do { let $id:ident := $t1:term ; $dd:dijkstra_do}) =>
  `((let $id := $t1; Do { $dd }))

| `(Do { with $t1:term using $t2:term ; $dd:dijkstra_do }) =>
  `(@DijkstraMonad.compD _ _ _ _ _ _ $t1 _ (Do { $dd }) $t2)

| `(Do { $t:dijkstra_singleton; $dd:dijkstra_do }) =>
  `(DijkstraMonad.bindD (DoSing {$t}) fun _ => Do { $dd } )

| `(Do { $t:dijkstra_singleton }) =>
  `(DoSing {$t})

#check DijkstraMonad.bindD

def test : ToDMonad Id Id.wp Nat (pure 1) := pureD 1
def test1 (i:Nat) : ToDMonad Id Id.wp Nat (pure (.succ i)) := pureD (i + 1)

def test' : ToDMonad Id Id.wp Nat (pure 2) := Do {
  let i ← test;
  test1 i
}

#print Id.wp
#print bindD

#check EffectObservation.θ

#check compD
def testST := toDMonad (StateT Nat Id) (StateT Nat Id.wp) (set 0 >>= fun _ => pure 1)
#reduce testST

def testST' : ToDMonad (StateT Nat Id) (StateT Nat Id.wp) Nat (θ' (StateT Nat Id) _ $ set 0 >>= fun _ => pure 2) :=
  compD (toDMonad _ _ (testST.val >>= fun x => pure (x+1))) (by
    intro x p h
    assumption
  )

#reduce θ' (StateT Nat Id) (StateT Nat Id.wp) <| set 0 >>= fun _ => pure 1
#reduce StateT Nat Id.wp
#check toDMonad
#reduce fun s:Nat => Id.wp.check (fun (x, s') => s = s' ∧ x ≥ 2)

def testst : ToDMonad (StateT Nat Id) (StateT Nat Id.wp) PUnit (set 0) :=
  compD (toDMonad _ _ $ set 0) (by
    intro s p h
    simp [θ, pure]
    simp [set, StateT.set, pure] at h
    simp [set, StateT.set]
    assumption
  )

#print ToDMonad

#reduce StateT Nat Id.wp Nat

def test2 : ToDMonad (StateT Nat Id) (StateT Nat Id.wp) Nat
  (fun s => Id.wp.check_pre_post (s = 1) fun (x, s') => s' = 0 ∧ x ≤ 2) :=
  Do {
      with set 0 >>= fun _ => pure 1 using (by
        intro s p
        simp [Id.wp.check_pre_post]
        intro h
        simp [bind, StateT.bind, pure, StateT.pure, set, StateT.set]
        apply h.2
        simp
      );
      toDMonad _ _ <| set 0 with θ (set 0) using (by
        intro s p
        simp [set, StateT.set, θ]
        intro h
        assumption
      );
      pureD 1
  }

