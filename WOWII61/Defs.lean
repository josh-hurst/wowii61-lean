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

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# Residue and Largest Induced Forest Definitions

Graph invariants from `google-deepmind/formal-conjectures`
(`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Residue.lean` and
`Induced.lean` at commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`).
The port preserves the defining equations and adapts the list-length and termination proofs.
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
