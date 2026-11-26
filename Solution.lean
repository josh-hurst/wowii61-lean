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

public import WOWII61

@[expose] public section

/-!
# Proved Solution

Supplies complete Lean 4 proofs of `WrittenOnTheWallII.GraphConjecture61.conjecture61` and
`WrittenOnTheWallII.GraphConjecture61.induced_matching_residue` as declared in `Challenge.lean`,
using only the three permitted standard Lean axioms (`propext`, `Quot.sound`, `Classical.choice`).
-/

namespace WrittenOnTheWallII.GraphConjecture61

open SimpleGraph

theorem induced_matching_residue {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] {k : ℕ} (a b : Fin k → α)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hdisj : Disjoint (Finset.univ.image a) (Finset.univ.image b))
    (hA : G.IsIndepSet ((Finset.univ.image a : Finset α) : Set α))
    (hB : G.IsIndepSet ((Finset.univ.image b : Finset α) : Set α))
    (hadj : ∀ i j : Fin k, G.Adj (a i) (b j) ↔ i = j) :
    residue G ≤
      max (G.induce { u : α | u ∉ Finset.univ.image a }).indepNum
        (G.induce { u : α | u ∉ Finset.univ.image b }).indepNum :=
  WOWII61.inducedMatchingResidue G
    ⟨a, b, Finset.univ.image a, Finset.univ.image b, rfl, rfl,
      by simpa using Finset.card_image_of_injective Finset.univ ha,
      by simpa using Finset.card_image_of_injective Finset.univ hb,
      hdisj, hA, hB, hadj⟩

theorem conjecture61 {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (residue G : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ (G.largestInducedForestSize : ℝ) :=
  WOWII61.realForestBound G h

end WrittenOnTheWallII.GraphConjecture61
