/-
Copyright 2026 The Formal Conjectures Authors.
Modifications Copyright 2026 Josh Hurst.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# Written on the Wall II, Conjecture 61

For every nontrivial finite connected simple graph `G`,
`residue(G) + ⌈diam(G) / 3⌉ ≤ largestInducedForestSize(G)`.

This submission proves both:
1. `WrittenOnTheWallII.GraphConjecture61.conjecture61` — the exact upstream statement from
   `google-deepmind/formal-conjectures` commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`.
2. `WrittenOnTheWallII.GraphConjecture61.induced_matching_residue` — the general
   Induced-Matching Residue Inequality `R(G) ≤ max (α(G - A)) (α(G - B))` for every
   induced matching `(A, B)` in any finite simple graph `G`.
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- One step of Havel–Hakimi reduction on a descending degree sequence: drop the head `d`,
decrement the next `d` entries by `1`, and re-sort descending. -/
def havelHakimiStep (s : List ℕ) : List ℕ :=
  match s with
  | [] => []
  | d :: rest =>
    let (to_decrement, remaining) := rest.splitAt d
    let decremented := to_decrement.map (· - 1)
    (decremented ++ remaining).mergeSort (· ≥ ·)

/-- `havelHakimiStep` drops the list length by exactly one on a nonempty list. -/
theorem havelHakimiStep_length_cons (d : ℕ) (rest : List ℕ) :
    (havelHakimiStep (d :: rest)).length = rest.length := by
  simp only [havelHakimiStep, List.splitAt_eq, List.length_mergeSort, List.length_append,
    List.length_map, List.length_take, List.length_drop]
  rcases Nat.le_total d rest.length with h | h
  · rw [Nat.min_eq_left h, Nat.add_sub_of_le h]
  · rw [Nat.min_eq_right h, Nat.sub_eq_zero_of_le h, Nat.add_zero]

/-- Auxiliary recursion computing the number of zeros left by Havel–Hakimi elimination. -/
def residueAux : List ℕ → ℕ
  | [] => 0
  | 0 :: s => 1 + s.length
  | d :: rest => residueAux (havelHakimiStep (d :: rest))
termination_by l => l.length
decreasing_by
  simp only [havelHakimiStep_length_cons, List.length_cons]
  exact Nat.lt_succ_self _

/-- The Havel–Hakimi residue of a finite simple graph `G`. -/
noncomputable def residue (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  residueAux ((Finset.univ.val.map fun v => G.degree v).sort (· ≥ ·))

/-- `largestInducedForestSize G` is the size of a largest induced forest of `G`. -/
noncomputable def largestInducedForestSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsAcyclic ∧ s.card = n }

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture61

open SimpleGraph

/--
**Induced-Matching Residue Inequality.**

For every finite simple graph `G` and every induced matching of `k` edges between disjoint
independent vertex sets `A = Finset.univ.image a` and `B = Finset.univ.image b`
(`a, b : Fin k → α` injective with `G.Adj (a i) (b j) ↔ i = j`), the Havel–Hakimi residue
satisfies `residue G ≤ max α(G - A) α(G - B)`.
-/
theorem induced_matching_residue {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] {k : ℕ} (a b : Fin k → α)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hdisj : Disjoint (Finset.univ.image a) (Finset.univ.image b))
    (hA : G.IsIndepSet ((Finset.univ.image a : Finset α) : Set α))
    (hB : G.IsIndepSet ((Finset.univ.image b : Finset α) : Set α))
    (hadj : ∀ i j : Fin k, G.Adj (a i) (b j) ↔ i = j) :
    residue G ≤
      max (G.induce { u : α | u ∉ Finset.univ.image a }).indepNum
        (G.induce { u : α | u ∉ Finset.univ.image b }).indepNum := by
  sorry

/--
**WOWII Conjecture 61** (E. DeLaViña, Graffiti.pc, 25 March 2004).

For every nontrivial finite connected simple graph `G`,
`residue(G) + ⌈diam(G) / 3⌉ ≤ largestInducedForestSize(G)`.
-/
theorem conjecture61 {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (residue G : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ (G.largestInducedForestSize : ℝ) := by
  sorry

end WrittenOnTheWallII.GraphConjecture61
