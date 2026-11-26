module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import WOWII61.Defs

/-!
# First-Isolation 2-Switch for WOWII Conjecture 61

This module formalizes:
1. The general degree-preserving 2-switch `twoSwitch Q v x y w`, obtained by deleting
   edges `{v, x}` and `{w, y}` and adding edges `{v, w}` and `{x, y}`:
   - pointwise degree preservation (`twoSwitch_degree_eq`),
   - Havel–Hakimi residue preservation (`twoSwitch_residue_eq`),
   - maximum-degree preservation (`twoSwitch_maxDegree_preserved`).
2. The elementary **First-Isolation Switch**: when `x` has sole neighbor `v` in `Q`,
   `y` is adjacent to `w`, and `vw`, `xy` are nonedges (with `v ≠ w`, `x ≠ y`),
   every independent set `I` in `H - v` yields an equal-size independent set `I'`
   in `Q - v` omitting `y` by replacing `y` with `x` (`firstIsolation_switch`,
   `firstIsolation_induce_indepSet_transfer`, `firstIsolation_indepNum_le`).
3. **Conditional boundary** (`firstIsolation_residue_le_indepNum_erase_vy_of_fms`):
   making explicit the Favaron–Mahéo–Saclé / max-degree-deletion premise under which
   the first-isolation switch implies `residue Q ≤ α(Q - {v, y})`.
4. **Disjoint-union forced-vertex 2-switch bound** (`disjointUnion_forced_twoSwitch_indepNum_le`
   and its conditional residue corollary): blocking disjoint-union counterexamples to IMR
   using the same `twoSwitch` operation.
-/

@[expose] public section

namespace WOWII61.FirstIsolation

open SimpleGraph Finset

section TwoSwitch

variable {V : Type*}

/-- The 2-switch of `Q` deleting `{v, x}` and `{w, y}` and adding `{v, w}` and `{x, y}`. -/
def twoSwitch (Q : SimpleGraph V) (v x y w : V) : SimpleGraph V :=
  (Q.deleteEdges {s(v, x), s(w, y)}) ⊔ SimpleGraph.fromEdgeSet {s(v, w), s(x, y)}

instance instDecidableRelTwoSwitch [DecidableEq V] (Q : SimpleGraph V) [DecidableRel Q.Adj]
    (v x y w : V) : DecidableRel (twoSwitch Q v x y w).Adj := fun a b =>
  decidable_of_iff
    ((Q.Adj a b ∧ s(a, b) ≠ s(v, x) ∧ s(a, b) ≠ s(w, y)) ∨
      ((s(a, b) = s(v, w) ∨ s(a, b) = s(x, y)) ∧ a ≠ b))
    (by
      simp [twoSwitch, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj,
        SimpleGraph.fromEdgeSet_adj, not_or])

/-- Exact adjacency characterization of `twoSwitch` when the two added pairs are non-loops. -/
theorem twoSwitch_adj_iff (Q : SimpleGraph V) {v x y w : V}
    (hne_vw : v ≠ w) (hne_xy : x ≠ y) (a b : V) :
    (twoSwitch Q v x y w).Adj a b ↔
      (Q.Adj a b ∧ s(a, b) ≠ s(v, x) ∧ s(a, b) ≠ s(w, y)) ∨
        s(a, b) = s(v, w) ∨ s(a, b) = s(x, y) := by
  simp only [twoSwitch, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj,
    SimpleGraph.fromEdgeSet_adj, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro (h | ⟨h | h, _⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl h
    · refine Or.inr ⟨Or.inl h, ?_⟩
      intro hab
      subst hab
      rw [Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hne_vw rfl
    · refine Or.inr ⟨Or.inr h, ?_⟩
      intro hab
      subst hab
      rw [Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hne_xy rfl

/-- The six pairwise distinctness facts implied by edges `vx`, `yw` and nonedges `vw`, `xy`. -/
theorem twoSwitch_distinct (Q : SimpleGraph V) {v x y w : V}
    (hvx : Q.Adj v x) (hyw : Q.Adj y w)
    (hvw : ¬ Q.Adj v w) (hxy : ¬ Q.Adj x y)
    (hne_vw : v ≠ w) (hne_xy : x ≠ y) :
    v ≠ x ∧ v ≠ y ∧ v ≠ w ∧ x ≠ y ∧ x ≠ w ∧ y ≠ w := by
  refine ⟨hvx.ne, ?_, hne_vw, hne_xy, ?_, hyw.ne⟩
  · intro hvy; exact hvw (hvy ▸ hyw)
  · intro hxw; exact hxy (hxw ▸ hyw.symm)

/-- In the first-isolation setting (`x` has sole neighbor `v`), `¬ Q.Adj x y` is automatic
from `y ~ w` and `¬ v ~ w`, so all six pairwise distinctness conditions follow. -/
theorem firstIsolation_distinct (Q : SimpleGraph V) {v x y w : V}
    (hsole : ∀ u, Q.Adj x u ↔ u = v) (hyw : Q.Adj y w)
    (hvw : ¬ Q.Adj v w) (hne_vw : v ≠ w) (hne_xy : x ≠ y) :
    Q.Adj v x ∧ ¬ Q.Adj x y ∧
      (v ≠ x ∧ v ≠ y ∧ v ≠ w ∧ x ≠ y ∧ x ≠ w ∧ y ≠ w) := by
  have hvx : Q.Adj v x := ((hsole v).mpr rfl).symm
  have hxy : ¬ Q.Adj x y := by
    intro h
    have hy : y = v := (hsole y).mp h
    exact hvw (hy ▸ hyw)
  exact ⟨hvx, hxy, twoSwitch_distinct Q hvx hyw hvw hxy hne_vw hne_xy⟩

section DegreePreservation

variable [Fintype V] [DecidableEq V]

omit [Fintype V] in
private lemma card_insert_erase_eq {s : Finset V} {a b : V}
    (ha : a ∈ s) (hb : b ∉ s) : (insert b (s.erase a)).card = s.card := by
  have hb' : b ∉ s.erase a := fun h => hb (mem_of_mem_erase h)
  rw [card_insert_of_notMem hb', card_erase_add_one ha]

theorem twoSwitch_neighborFinset_v (Q : SimpleGraph V) [DecidableRel Q.Adj] {v x y w : V}
    (hvx : Q.Adj v x) (hyw : Q.Adj y w)
    (hvw : ¬ Q.Adj v w) (hxy : ¬ Q.Adj x y)
    (hne_vw : v ≠ w) (hne_xy : x ≠ y) :
    (twoSwitch Q v x y w).neighborFinset v = insert w ((Q.neighborFinset v).erase x) := by
  obtain ⟨hvx_ne, hvy_ne, _, _, _, _⟩ :=
    twoSwitch_distinct Q hvx hyw hvw hxy hne_vw hne_xy
  ext z
  simp only [SimpleGraph.mem_neighborFinset, twoSwitch_adj_iff Q hne_vw hne_xy, mem_insert,
    mem_erase, Sym2.eq_iff, ne_eq, true_and]
  constructor
  · rintro (⟨hz, h1, _⟩ | (rfl | ⟨hvw', _⟩) | (⟨hvx', _⟩ | ⟨hvy', _⟩))
    · right
      exact ⟨fun hzx => h1 (Or.inl hzx), hz⟩
    · exact Or.inl rfl
    · exact absurd hvw' hne_vw
    · exact absurd hvx' hvx_ne
    · exact absurd hvy' hvy_ne
  · rintro (rfl | ⟨hzx, hz⟩)
    · exact Or.inr (Or.inl (Or.inl rfl))
    · refine Or.inl ⟨hz, ?_, ?_⟩
      · rintro (h | ⟨h, _⟩)
        · exact hzx h
        · exact hvx_ne h
      · rintro (⟨h, _⟩ | ⟨h, _⟩)
        · exact hne_vw h
        · exact hvy_ne h

theorem twoSwitch_neighborFinset_x (Q : SimpleGraph V) [DecidableRel Q.Adj] {v x y w : V}
    (hvx : Q.Adj v x) (hyw : Q.Adj y w)
    (hvw : ¬ Q.Adj v w) (hxy : ¬ Q.Adj x y)
    (hne_vw : v ≠ w) (hne_xy : x ≠ y) :
    (twoSwitch Q v x y w).neighborFinset x = insert y ((Q.neighborFinset x).erase v) := by
  obtain ⟨hvx_ne, _, _, _, hxw_ne, _⟩ :=
    twoSwitch_distinct Q hvx hyw hvw hxy hne_vw hne_xy
  ext z
  simp only [SimpleGraph.mem_neighborFinset, twoSwitch_adj_iff Q hne_vw hne_xy, mem_insert,
    mem_erase, Sym2.eq_iff, ne_eq, true_and]
  constructor
  · rintro (⟨hz, h1, _⟩ | (⟨hxv', _⟩ | ⟨hxw', _⟩) | (rfl | ⟨hxy', _⟩))
    · right
      exact ⟨fun hzv => h1 (Or.inr hzv), hz⟩
    · exact absurd hxv'.symm hvx_ne
    · exact absurd hxw' hxw_ne
    · exact Or.inl rfl
    · exact absurd hxy' hne_xy
  · rintro (rfl | ⟨hzv, hz⟩)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · refine Or.inl ⟨hz, ?_, ?_⟩
      · rintro (⟨h, _⟩ | h)
        · exact hvx_ne h.symm
        · exact hzv h
      · rintro (⟨h, _⟩ | ⟨h, _⟩)
        · exact hxw_ne h
        · exact hne_xy h

theorem twoSwitch_neighborFinset_y (Q : SimpleGraph V) [DecidableRel Q.Adj] {v x y w : V}
    (hvx : Q.Adj v x) (hyw : Q.Adj y w)
    (hvw : ¬ Q.Adj v w) (hxy : ¬ Q.Adj x y)
    (hne_vw : v ≠ w) (hne_xy : x ≠ y) :
    (twoSwitch Q v x y w).neighborFinset y = insert x ((Q.neighborFinset y).erase w) := by
  obtain ⟨_, hvy_ne, _, _, _, hyw_ne⟩ :=
    twoSwitch_distinct Q hvx hyw hvw hxy hne_vw hne_xy
  ext z
  simp only [SimpleGraph.mem_neighborFinset, twoSwitch_adj_iff Q hne_vw hne_xy, mem_insert,
    mem_erase, Sym2.eq_iff, ne_eq, true_and]
  constructor
  · rintro (⟨hz, _, h2⟩ | (⟨hyv', _⟩ | ⟨hyw', _⟩) | (⟨hyx', _⟩ | rfl))
    · right
      exact ⟨fun hzw => h2 (Or.inr hzw), hz⟩
    · exact absurd hyv'.symm hvy_ne
    · exact absurd hyw' hyw_ne
    · exact absurd hyx'.symm hne_xy
    · exact Or.inl rfl
  · rintro (rfl | ⟨hzw, hz⟩)
    · exact Or.inr (Or.inr (Or.inr rfl))
    · refine Or.inl ⟨hz, ?_, ?_⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩)
        · exact hvy_ne h.symm
        · exact hne_xy h.symm
      · rintro (⟨h, _⟩ | h)
        · exact hyw_ne h
        · exact hzw h

theorem twoSwitch_neighborFinset_w (Q : SimpleGraph V) [DecidableRel Q.Adj] {v x y w : V}
    (hvx : Q.Adj v x) (hyw : Q.Adj y w)
    (hvw : ¬ Q.Adj v w) (hxy : ¬ Q.Adj x y)
    (hne_vw : v ≠ w) (hne_xy : x ≠ y) :
    (twoSwitch Q v x y w).neighborFinset w = insert v ((Q.neighborFinset w).erase y) := by
  obtain ⟨_, _, _, _, hxw_ne, hyw_ne⟩ :=
    twoSwitch_distinct Q hvx hyw hvw hxy hne_vw hne_xy
  ext z
  simp only [SimpleGraph.mem_neighborFinset, twoSwitch_adj_iff Q hne_vw hne_xy, mem_insert,
    mem_erase, Sym2.eq_iff, ne_eq, true_and]
  constructor
  · rintro (⟨hz, _, h2⟩ | (⟨hwv', _⟩ | rfl) | (⟨hwx', _⟩ | ⟨hwy', _⟩))
    · right
      exact ⟨fun hzy => h2 (Or.inl hzy), hz⟩
    · exact absurd hwv'.symm hne_vw
    · exact Or.inl rfl
    · exact absurd hwx'.symm hxw_ne
    · exact absurd hwy'.symm hyw_ne
  · rintro (rfl | ⟨hzy, hz⟩)
    · exact Or.inr (Or.inl (Or.inr rfl))
    · refine Or.inl ⟨hz, ?_, ?_⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩)
        · exact hne_vw h.symm
        · exact hxw_ne h.symm
      · rintro (h | ⟨h, _⟩)
        · exact hzy h
        · exact hyw_ne h.symm

theorem twoSwitch_neighborFinset_other (Q : SimpleGraph V) [DecidableRel Q.Adj] {v x y w u : V}
    (hne_vw : v ≠ w) (hne_xy : x ≠ y)
    (huv : u ≠ v) (hux : u ≠ x) (huy : u ≠ y) (huw : u ≠ w) :
    (twoSwitch Q v x y w).neighborFinset u = Q.neighborFinset u := by
  ext z
  simp only [SimpleGraph.mem_neighborFinset, twoSwitch_adj_iff Q hne_vw hne_xy, Sym2.eq_iff, ne_eq]
  constructor
  · rintro (⟨hz, _, _⟩ | (⟨h, _⟩ | ⟨h, _⟩) | (⟨h, _⟩ | ⟨h, _⟩))
    · exact hz
    · exact absurd h huv
    · exact absurd h huw
    · exact absurd h hux
    · exact absurd h huy
  · intro hz
    refine Or.inl ⟨hz, ?_, ?_⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact huv h
      · exact hux h
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact huw h
      · exact huy h

/-- Every 2-switch preserves vertex degrees pointwise. -/
theorem twoSwitch_degree_eq (Q : SimpleGraph V) [DecidableRel Q.Adj] {v x y w : V}
    (hvx : Q.Adj v x) (hyw : Q.Adj y w)
    (hvw : ¬ Q.Adj v w) (hxy : ¬ Q.Adj x y)
    (hne_vw : v ≠ w) (hne_xy : x ≠ y) (u : V) :
    (twoSwitch Q v x y w).degree u = Q.degree u := by
  simp only [SimpleGraph.degree]
  by_cases huv : u = v
  · rw [huv, twoSwitch_neighborFinset_v Q hvx hyw hvw hxy hne_vw hne_xy]
    exact card_insert_erase_eq ((Q.mem_neighborFinset v x).mpr hvx)
      (by simpa [SimpleGraph.mem_neighborFinset] using hvw)
  · by_cases hux : u = x
    · rw [hux, twoSwitch_neighborFinset_x Q hvx hyw hvw hxy hne_vw hne_xy]
      exact card_insert_erase_eq ((Q.mem_neighborFinset x v).mpr hvx.symm)
        (by simpa [SimpleGraph.mem_neighborFinset] using hxy)
    · by_cases huy : u = y
      · rw [huy, twoSwitch_neighborFinset_y Q hvx hyw hvw hxy hne_vw hne_xy]
        exact card_insert_erase_eq ((Q.mem_neighborFinset y w).mpr hyw)
          (by simpa [SimpleGraph.mem_neighborFinset] using fun h : Q.Adj y x => hxy h.symm)
      · by_cases huw : u = w
        · rw [huw, twoSwitch_neighborFinset_w Q hvx hyw hvw hxy hne_vw hne_xy]
          exact card_insert_erase_eq ((Q.mem_neighborFinset w y).mpr hyw.symm)
            (by simpa [SimpleGraph.mem_neighborFinset] using fun h : Q.Adj w v => hvw h.symm)
        · rw [twoSwitch_neighborFinset_other Q hne_vw hne_xy huv hux huy huw]

/-- Every 2-switch preserves the exact upstream Havel–Hakimi `SimpleGraph.residue`. -/
theorem twoSwitch_residue_eq (Q : SimpleGraph V) [DecidableRel Q.Adj] {v x y w : V}
    (hvx : Q.Adj v x) (hyw : Q.Adj y w)
    (hvw : ¬ Q.Adj v w) (hxy : ¬ Q.Adj x y)
    (hne_vw : v ≠ w) (hne_xy : x ≠ y) :
    SimpleGraph.residue (twoSwitch Q v x y w) = SimpleGraph.residue Q := by
  unfold SimpleGraph.residue
  have hdeg : (fun u => (twoSwitch Q v x y w).degree u) = fun u => Q.degree u := by
    funext u
    exact twoSwitch_degree_eq Q hvx hyw hvw hxy hne_vw hne_xy u
  rw [hdeg]

/-- If `v` has maximum degree in `Q`, then `v` remains a maximum-degree vertex after a 2-switch. -/
theorem twoSwitch_maxDegree_preserved (Q : SimpleGraph V) [DecidableRel Q.Adj] {v x y w : V}
    (hvx : Q.Adj v x) (hyw : Q.Adj y w)
    (hvw : ¬ Q.Adj v w) (hxy : ¬ Q.Adj x y)
    (hne_vw : v ≠ w) (hne_xy : x ≠ y)
    (hmax : ∀ u, Q.degree u ≤ Q.degree v) :
    ∀ u, (twoSwitch Q v x y w).degree u ≤ (twoSwitch Q v x y w).degree v := by
  intro u
  rw [twoSwitch_degree_eq Q hvx hyw hvw hxy hne_vw hne_xy u,
    twoSwitch_degree_eq Q hvx hyw hvw hxy hne_vw hne_xy v]
  exact hmax u

end DegreePreservation

end TwoSwitch

/-! ## Elementary First-Isolation Switch -/

section FirstIsolationSwitch

variable {V : Type*} [DecidableEq V]

/-- Replace `y` by `x` in `I` when `y ∈ I`, and leave `I` unchanged otherwise. -/
def replaceYWithX (x y : V) (I : Finset V) : Finset V :=
  if y ∈ I then insert x (I.erase y) else I

theorem replaceYWithX_not_mem_y {x y : V} (hne_xy : x ≠ y) (I : Finset V) :
    y ∉ replaceYWithX x y I := by
  unfold replaceYWithX
  split_ifs with hy
  · simp [hne_xy.symm]
  · exact hy

theorem replaceYWithX_not_mem_v {v x y : V} (hne_vx : v ≠ x) {I : Finset V} (hv : v ∉ I) :
    v ∉ replaceYWithX x y I := by
  unfold replaceYWithX
  split_ifs with hy
  · simp only [mem_insert, mem_erase, not_or, not_and]
    exact ⟨hne_vx, fun _ => hv⟩
  · exact hv

theorem firstIsolation_replace_card (Q : SimpleGraph V) {v x y w : V}
    (hne_vw : v ≠ w) (hne_xy : x ≠ y)
    {I : Finset V} (hI : (twoSwitch Q v x y w).IsIndepSet (I : Set V)) :
    (replaceYWithX x y I).card = I.card := by
  unfold replaceYWithX
  split_ifs with hy
  · have hxy_H : (twoSwitch Q v x y w).Adj x y :=
      (twoSwitch_adj_iff Q hne_vw hne_xy x y).mpr (Or.inr (Or.inr rfl))
    have hx_not_I : x ∉ I := by
      intro hx
      exact hI (mem_coe.mpr hx) (mem_coe.mpr hy) hne_xy hxy_H
    have hx_not_erase : x ∉ I.erase y := fun h => hx_not_I (mem_of_mem_erase h)
    rw [card_insert_of_notMem hx_not_erase, card_erase_add_one hy]
  · rfl

theorem firstIsolation_replace_isIndepSet (Q : SimpleGraph V) {v x y w : V}
    (hsole : ∀ u, Q.Adj x u ↔ u = v)
    (hne_vw : v ≠ w) (hne_xy : x ≠ y)
    {I : Finset V} (hI : (twoSwitch Q v x y w).IsIndepSet (I : Set V)) (hv : v ∉ I) :
    Q.IsIndepSet ((replaceYWithX x y I) : Set V) := by
  have hvx : Q.Adj v x := ((hsole v).mpr rfl).symm
  have hv_not_I' : v ∉ replaceYWithX x y I := replaceYWithX_not_mem_v hvx.ne hv
  have hy_not_I' : y ∉ replaceYWithX x y I := replaceYWithX_not_mem_y hne_xy I
  have mem_I_of_ne_x : ∀ z ∈ replaceYWithX x y I, z ≠ x → z ∈ I := by
    intro z hz hzx
    unfold replaceYWithX at hz
    split_ifs at hz with hy
    · simp only [mem_insert, mem_erase] at hz
      rcases hz with rfl | ⟨_, hzI⟩
      · exact absurd rfl hzx
      · exact hzI
    · exact hz
  intro a ha b hb hab hQab
  rw [mem_coe] at ha hb
  by_cases hax : a = x
  · subst hax
    have hbv : b = v := (hsole b).mp hQab
    exact hv_not_I' (hbv ▸ hb)
  · by_cases hbx : b = x
    · subst hbx
      have hav : a = v := (hsole a).mp hQab.symm
      exact hv_not_I' (hav ▸ ha)
    · have haI : a ∈ I := mem_I_of_ne_x a ha hax
      have hbI : b ∈ I := mem_I_of_ne_x b hb hbx
      have hav : a ≠ v := fun h => hv_not_I' (h ▸ ha)
      have hbv : b ≠ v := fun h => hv_not_I' (h ▸ hb)
      have hay : a ≠ y := fun h => hy_not_I' (h ▸ ha)
      have hby : b ≠ y := fun h => hy_not_I' (h ▸ hb)
      have hHab : (twoSwitch Q v x y w).Adj a b := by
        rw [twoSwitch_adj_iff Q hne_vw hne_xy]
        refine Or.inl ⟨hQab, ?_, ?_⟩
        · simp only [ne_eq, Sym2.eq_iff, not_or, not_and]
          exact ⟨fun h _ => hav h, fun _ h => hbv h⟩
        · simp only [ne_eq, Sym2.eq_iff, not_or, not_and]
          exact ⟨fun _ h => hby h, fun h _ => hay h⟩
      exact hI (mem_coe.mpr haI) (mem_coe.mpr hbI) hab hHab

/--
**Elementary First-Isolation Switch Theorem (complete package).**

Given a finite simple graph `Q` and vertices `v, x, y, w` such that:
- `x` has sole neighbor `v` in `Q`,
- `y` is adjacent to `w` in `Q`,
- `v w` and `x y` are nonedges (`¬ Q.Adj v w`, `¬ Q.Adj x y`, `v ≠ w`, `x ≠ y`),

let `H = twoSwitch Q v x y w` (deleting `vx, wy` and adding `vw, xy`). Then:
1. `H` has the same degree as `Q` at every vertex (and the same `residue`),
2. if `v` has maximum degree in `Q`, then `v` remains a maximum-degree vertex in `H`,
3. every independent set `I` of `H` avoiding `v` yields an equal-size independent set `I'`
   of `Q` avoiding both `v` and `y` (`I' = replaceYWithX x y I`).
-/
theorem firstIsolation_switch [Fintype V] (Q : SimpleGraph V) [DecidableRel Q.Adj]
    {v x y w : V}
    (hsole : ∀ u, Q.Adj x u ↔ u = v)
    (hyw : Q.Adj y w)
    (hvw : ¬ Q.Adj v w) (hxy : ¬ Q.Adj x y)
    (hne_vw : v ≠ w) (hne_xy : x ≠ y) :
    let H := twoSwitch Q v x y w
    (∀ u, H.degree u = Q.degree u) ∧
    SimpleGraph.residue H = SimpleGraph.residue Q ∧
    ((∀ u, Q.degree u ≤ Q.degree v) → ∀ u, H.degree u ≤ H.degree v) ∧
    (∀ I : Finset V, H.IsIndepSet (I : Set V) → v ∉ I →
      let I' := replaceYWithX x y I
      Q.IsIndepSet (I' : Set V) ∧ v ∉ I' ∧ y ∉ I' ∧ I'.card = I.card) := by
  have hvx : Q.Adj v x := ((hsole v).mpr rfl).symm
  refine ⟨twoSwitch_degree_eq Q hvx hyw hvw hxy hne_vw hne_xy,
    twoSwitch_residue_eq Q hvx hyw hvw hxy hne_vw hne_xy,
    twoSwitch_maxDegree_preserved Q hvx hyw hvw hxy hne_vw hne_xy,
    fun I hI hv => ?_⟩
  exact ⟨firstIsolation_replace_isIndepSet Q hsole hne_vw hne_xy hI hv,
    replaceYWithX_not_mem_v hvx.ne hv,
    replaceYWithX_not_mem_y hne_xy I,
    firstIsolation_replace_card Q hne_vw hne_xy hI⟩

/-- Induced-subgraph version of the independent-set transfer: every independent set in `H - v`
yields an equal-size independent set in `Q - {v, y}`. -/
theorem firstIsolation_induce_indepSet_transfer (Q : SimpleGraph V) {v x y w : V}
    (hsole : ∀ u, Q.Adj x u ↔ u = v)
    (hne_vw : v ≠ w) (hne_xy : x ≠ y)
    (S : Finset { u : V // u ≠ v })
    (hS : ((twoSwitch Q v x y w).induce { u : V | u ≠ v }).IsIndepSet (S : Set { u : V // u ≠ v })) :
    ∃ S' : Finset { u : V // u ≠ v ∧ u ≠ y },
      (Q.induce { u : V | u ≠ v ∧ u ≠ y }).IsIndepSet (S' : Set { u : V // u ≠ v ∧ u ≠ y }) ∧
        S'.card = S.card := by
  have hvx : Q.Adj v x := ((hsole v).mpr rfl).symm
  let I : Finset V := S.map ⟨Subtype.val, Subtype.val_injective⟩
  have hI_indep : (twoSwitch Q v x y w).IsIndepSet (I : Set V) := by
    intro a ha b hb hab
    rw [mem_coe, mem_map] at ha hb
    rcases ha with ⟨⟨a', ha'⟩, haS, rfl⟩
    rcases hb with ⟨⟨b', hb'⟩, hbS, rfl⟩
    have hne : (⟨a', ha'⟩ : { u : V // u ≠ v }) ≠ ⟨b', hb'⟩ := fun h =>
      hab (congrArg Subtype.val h)
    exact hS (mem_coe.mpr haS) (mem_coe.mpr hbS) hne
  have hv_not_I : v ∉ I := by
    simp only [I, mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
    rintro ⟨u, hu⟩ _ huv
    exact hu huv
  let I' : Finset V := replaceYWithX x y I
  have hI'_indep : Q.IsIndepSet (I' : Set V) :=
    firstIsolation_replace_isIndepSet Q hsole hne_vw hne_xy hI_indep hv_not_I
  have hv_not_I' : v ∉ I' := replaceYWithX_not_mem_v hvx.ne hv_not_I
  have hy_not_I' : y ∉ I' := replaceYWithX_not_mem_y hne_xy I
  have hI'_card : I'.card = S.card := by
    rw [firstIsolation_replace_card Q hne_vw hne_xy hI_indep, card_map]
  have hmem_pred : ∀ u ∈ I', u ≠ v ∧ u ≠ y := fun u hu =>
    ⟨fun h => hv_not_I' (h ▸ hu), fun h => hy_not_I' (h ▸ hu)⟩
  let S' : Finset { u : V // u ≠ v ∧ u ≠ y } :=
    I'.attach.map ⟨fun u => ⟨u.1, hmem_pred u.1 u.2⟩, by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun z : { u : V // u ≠ v ∧ u ≠ y } => z.1) hab⟩
  refine ⟨S', ?_, ?_⟩
  · intro a ha b hb hab
    rw [mem_coe, mem_map] at ha hb
    rcases ha with ⟨a0, _, rfl⟩
    rcases hb with ⟨b0, _, rfl⟩
    have hne : a0.1 ≠ b0.1 := fun h => hab (Subtype.ext h)
    exact hI'_indep (mem_coe.mpr a0.2) (mem_coe.mpr b0.2) hne
  · simp [S', hI'_card]

/-- Independence-number inequality for the first-isolation switch:
`α(H - v) ≤ α(Q - {v, y})`. -/
theorem firstIsolation_indepNum_le [Fintype V] (Q : SimpleGraph V) {v x y w : V}
    (hsole : ∀ u, Q.Adj x u ↔ u = v)
    (hne_vw : v ≠ w) (hne_xy : x ≠ y) :
    ((twoSwitch Q v x y w).induce { u : V | u ≠ v }).indepNum ≤
      (Q.induce { u : V | u ≠ v ∧ u ≠ y }).indepNum := by
  obtain ⟨S, hS⟩ := ((twoSwitch Q v x y w).induce { u : V | u ≠ v }).exists_isNIndepSet_indepNum
  obtain ⟨S', hS'_indep, hS'_card⟩ :=
    firstIsolation_induce_indepSet_transfer Q hsole hne_vw hne_xy S hS.isIndepSet
  calc
    ((twoSwitch Q v x y w).induce { u : V | u ≠ v }).indepNum = S.card := hS.card_eq.symm
    _ = S'.card := hS'_card.symm
    _ ≤ (Q.induce { u : V | u ≠ v ∧ u ≠ y }).indepNum := hS'_indep.card_le_indepNum

/-- Monotonicity corollary: `α(H - v) ≤ α(Q - y)`. -/
theorem firstIsolation_indepNum_le_erase_y [Fintype V] (Q : SimpleGraph V) {v x y w : V}
    (hsole : ∀ u, Q.Adj x u ↔ u = v)
    (hne_vw : v ≠ w) (hne_xy : x ≠ y) :
    ((twoSwitch Q v x y w).induce { u : V | u ≠ v }).indepNum ≤
      (Q.induce { u : V | u ≠ y }).indepNum := by
  obtain ⟨S, hS⟩ := (Q.induce { u : V | u ≠ v ∧ u ≠ y }).exists_isNIndepSet_indepNum
  let T : Finset { u : V // u ≠ y } :=
    S.map ⟨fun (u : { u : V // u ≠ v ∧ u ≠ y }) => ⟨u.1, u.2.2⟩, fun a b h =>
      Subtype.ext (congrArg (fun z : { u : V // u ≠ y } => z.1) h)⟩
  have hT_indep : (Q.induce { u : V | u ≠ y }).IsIndepSet (T : Set { u : V // u ≠ y }) := by
    intro a ha b hb hab
    rw [mem_coe, mem_map] at ha hb
    rcases ha with ⟨a0, ha0, rfl⟩
    rcases hb with ⟨b0, hb0, rfl⟩
    have hne : a0 ≠ b0 := fun h => hab (by subst h; rfl)
    exact hS.isIndepSet (mem_coe.mpr ha0) (mem_coe.mpr hb0) hne
  have hle : (Q.induce { u : V | u ≠ v ∧ u ≠ y }).indepNum ≤
      (Q.induce { u : V | u ≠ y }).indepNum := by
    calc
      (Q.induce { u : V | u ≠ v ∧ u ≠ y }).indepNum = S.card := hS.card_eq.symm
      _ = T.card := (card_map _).symm
      _ ≤ (Q.induce { u : V | u ≠ y }).indepNum := hT_indep.card_le_indepNum
  exact (firstIsolation_indepNum_le Q hsole hne_vw hne_xy).trans hle

/--
**CONDITIONAL BOUNDARY (explicit FMS + max-degree-deletion premise):**
If the switched graph `H = twoSwitch Q v x y w` satisfies the Favaron–Mahéo–Saclé /
max-degree-deletion inequality `residue H ≤ α(H - v)` (where `v` remains a max-degree
vertex of `H`), then `residue Q ≤ α(Q - {v, y})` and `residue Q ≤ α(Q - y)`.

Note: the general Favaron–Mahéo–Saclé theorem (`residue G ≤ α(G)`) and Triesch's
max-degree deletion monotonicity (`residue G ≤ residue (G - v)` for max-degree `v` with
`deg v ≥ 1`) are NOT imported here and are passed explicitly as `hFMS_del`.
-/
theorem firstIsolation_residue_le_indepNum_erase_vy_of_fms [Fintype V]
    (Q : SimpleGraph V) [DecidableRel Q.Adj] {v x y w : V}
    (hsole : ∀ u, Q.Adj x u ↔ u = v)
    (hyw : Q.Adj y w)
    (hvw : ¬ Q.Adj v w) (hxy : ¬ Q.Adj x y)
    (hne_vw : v ≠ w) (hne_xy : x ≠ y)
    (hFMS_del :
      SimpleGraph.residue (twoSwitch Q v x y w) ≤
        ((twoSwitch Q v x y w).induce { u : V | u ≠ v }).indepNum) :
    SimpleGraph.residue Q ≤ (Q.induce { u : V | u ≠ v ∧ u ≠ y }).indepNum ∧
      SimpleGraph.residue Q ≤ (Q.induce { u : V | u ≠ y }).indepNum := by
  have hvx : Q.Adj v x := ((hsole v).mpr rfl).symm
  have hres : SimpleGraph.residue Q = SimpleGraph.residue (twoSwitch Q v x y w) :=
    (twoSwitch_residue_eq Q hvx hyw hvw hxy hne_vw hne_xy).symm
  constructor
  · exact hres ▸ hFMS_del.trans (firstIsolation_indepNum_le Q hsole hne_vw hne_xy)
  · exact hres ▸ hFMS_del.trans (firstIsolation_indepNum_le_erase_y Q hsole hne_vw hne_xy)

end FirstIsolationSwitch

/-! ## Disjoint-Union Forced-Vertex 2-Switch Obstruction (Theorem 6) -/

section DisjointUnionTwoSwitch

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex `u` in `P` is *forced* in `Q[P]` if every independent set of `Q` contained in `P`
that omits `u` has cardinality strictly smaller than `α(Q[P])`. -/
def IsForcedInPart (Q : SimpleGraph V) (P : V → Prop) (u : V) : Prop :=
  ∀ S : Finset V, (∀ z ∈ S, P z) → Q.IsIndepSet (S : Set V) → u ∉ S →
    S.card + 1 ≤ (Q.induce { z : V | P z }).indepNum

omit [DecidableEq V] in
private lemma card_le_indepNum_induce_of_subset (Q : SimpleGraph V) (P : V → Prop)
    {S : Finset V} (hP : ∀ z ∈ S, P z) (hS : Q.IsIndepSet (S : Set V)) :
    S.card ≤ (Q.induce { z : V | P z }).indepNum := by
  let S' : Finset { z : V // P z } :=
    S.attach.map ⟨fun (z : { z : V // z ∈ S }) => ⟨z.1, hP z.1 z.2⟩, fun a b h =>
      Subtype.ext (congrArg (fun x : { z : V // P z } => x.1) h)⟩
  have hS'_indep : (Q.induce { z : V | P z }).IsIndepSet (S' : Set { z : V // P z }) := by
    intro a ha b hb hab
    rw [mem_coe, mem_map] at ha hb
    rcases ha with ⟨a0, _, rfl⟩
    rcases hb with ⟨b0, _, rfl⟩
    have hne : a0.1 ≠ b0.1 := fun h => hab (Subtype.ext h)
    exact hS (mem_coe.mpr a0.2) (mem_coe.mpr b0.2) hne
  calc
    S.card = S'.card := by simp [S']
    _ ≤ (Q.induce { z : V | P z }).indepNum := hS'_indep.card_le_indepNum

/--
**Disjoint-Union Forced-Vertex 2-Switch Theorem:**
Suppose `Q` splits into two parts `{z | P z}` and `{z | ¬ P z}` with no crossing edges,
`a₁ ~ b₁` lies in the first part with `b₁` forced, and `a₂ ~ b₂` lies in the second part
with `a₂` forced. Then the 2-switch `H = twoSwitch Q a₁ b₁ a₂ b₂` (deleting `a₁b₁, b₂a₂`
and adding `a₁b₂, b₁a₂`) preserves all degrees and `residue`, and satisfies
`H.indepNum + 1 ≤ α(Q[P]) + α(Q[¬ P])`.
-/
theorem disjointUnion_forced_twoSwitch_indepNum_le
    (Q : SimpleGraph V) [DecidableRel Q.Adj] (P : V → Prop) [DecidablePred P]
    {a₁ b₁ a₂ b₂ : V}
    (hsplit : ∀ u w, Q.Adj u w → (P u ↔ P w))
    (ha₁ : P a₁) (hb₁ : P b₁) (ha₂ : ¬ P a₂) (hb₂ : ¬ P b₂)
    (he₁ : Q.Adj a₁ b₁) (he₂ : Q.Adj a₂ b₂)
    (hforced₁ : IsForcedInPart Q P b₁)
    (hforced₂ : IsForcedInPart Q (fun z => ¬ P z) a₂) :
    let H := twoSwitch Q a₁ b₁ a₂ b₂
    (∀ u, H.degree u = Q.degree u) ∧
    SimpleGraph.residue H = SimpleGraph.residue Q ∧
    H.indepNum + 1 ≤
      (Q.induce { z : V | P z }).indepNum + (Q.induce { z : V | ¬ P z }).indepNum := by
  have hne_a1b2 : a₁ ≠ b₂ := fun h => hb₂ (h ▸ ha₁)
  have hne_b1a2 : b₁ ≠ a₂ := fun h => ha₂ (h ▸ hb₁)
  have hna1b2 : ¬ Q.Adj a₁ b₂ := fun h => hb₂ ((hsplit a₁ b₂ h).mp ha₁)
  have hnb1a2 : ¬ Q.Adj b₁ a₂ := fun h => ha₂ ((hsplit b₁ a₂ h).mp hb₁)
  refine ⟨twoSwitch_degree_eq Q he₁ he₂ hna1b2 hnb1a2 hne_a1b2 hne_b1a2,
    twoSwitch_residue_eq Q he₁ he₂ hna1b2 hnb1a2 hne_a1b2 hne_b1a2, ?_⟩
  let H := twoSwitch Q a₁ b₁ a₂ b₂
  obtain ⟨I, hI⟩ := H.exists_isNIndepSet_indepNum
  have hI_indep : H.IsIndepSet (I : Set V) := hI.isIndepSet
  rw [← hI.card_eq]
  let I₁ : Finset V := I.filter P
  let I₂ : Finset V := I.filter (fun z => ¬ P z)
  have hcard_split : I.card = I₁.card + I₂.card := by
    have hdisj : Disjoint I₁ I₂ := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      exact (mem_filter.mp hz2).2 (mem_filter.mp hz1).2
    have hunion : I₁ ∪ I₂ = I := by
      ext z
      simp only [I₁, I₂, mem_union, mem_filter]
      tauto
    rw [← card_union_of_disjoint hdisj, hunion]
  have hI₁_P : ∀ z ∈ I₁, P z := fun z hz => (mem_filter.mp hz).2
  have hI₂_nP : ∀ z ∈ I₂, ¬ P z := fun z hz => (mem_filter.mp hz).2
  have hH_a1b2 : H.Adj a₁ b₂ :=
    (twoSwitch_adj_iff Q hne_a1b2 hne_b1a2 a₁ b₂).mpr (Or.inr (Or.inl rfl))
  have hH_b1a2 : H.Adj b₁ a₂ :=
    (twoSwitch_adj_iff Q hne_a1b2 hne_b1a2 b₁ a₂).mpr (Or.inr (Or.inr rfl))
  have hQ_sub_part1 : ∀ S : Finset V, S ⊆ I₁ → ¬ (a₁ ∈ S ∧ b₁ ∈ S) → Q.IsIndepSet (S : Set V) := by
    intro S hSI hnotboth u hu w hw huw hQuw
    rw [mem_coe] at hu hw
    have huI₁ : u ∈ I₁ := hSI hu
    have hwI₁ : w ∈ I₁ := hSI hw
    have huI : u ∈ I := (mem_filter.mp huI₁).1
    have hwI : w ∈ I := (mem_filter.mp hwI₁).1
    have hHu : H.Adj u w := by
      rw [twoSwitch_adj_iff Q hne_a1b2 hne_b1a2]
      refine Or.inl ⟨hQuw, ?_, ?_⟩
      · simp only [ne_eq, Sym2.eq_iff, not_or, not_and]
        exact ⟨fun h1 h2 => hnotboth ⟨h1 ▸ hu, h2 ▸ hw⟩, fun h1 h2 => hnotboth ⟨h2 ▸ hw, h1 ▸ hu⟩⟩
      · simp only [ne_eq, Sym2.eq_iff, not_or, not_and]
        exact ⟨fun h _ => hb₂ (h ▸ hI₁_P u huI₁), fun h _ => ha₂ (h ▸ hI₁_P u huI₁)⟩
    exact hI_indep (mem_coe.mpr huI) (mem_coe.mpr hwI) huw hHu
  have hQ_sub_part2 : ∀ S : Finset V, S ⊆ I₂ → ¬ (a₂ ∈ S ∧ b₂ ∈ S) → Q.IsIndepSet (S : Set V) := by
    intro S hSI hnotboth u hu w hw huw hQuw
    rw [mem_coe] at hu hw
    have huI₂ : u ∈ I₂ := hSI hu
    have hwI₂ : w ∈ I₂ := hSI hw
    have huI : u ∈ I := (mem_filter.mp huI₂).1
    have hwI : w ∈ I := (mem_filter.mp hwI₂).1
    have hHu : H.Adj u w := by
      rw [twoSwitch_adj_iff Q hne_a1b2 hne_b1a2]
      refine Or.inl ⟨hQuw, ?_, ?_⟩
      · simp only [ne_eq, Sym2.eq_iff, not_or, not_and]
        exact ⟨fun h _ => hI₂_nP u huI₂ (h ▸ ha₁), fun h _ => hI₂_nP u huI₂ (h ▸ hb₁)⟩
      · simp only [ne_eq, Sym2.eq_iff, not_or, not_and]
        exact ⟨fun h1 h2 => hnotboth ⟨h2 ▸ hw, h1 ▸ hu⟩, fun h1 h2 => hnotboth ⟨h1 ▸ hu, h2 ▸ hw⟩⟩
    exact hI_indep (mem_coe.mpr huI) (mem_coe.mpr hwI) huw hHu
  rw [hcard_split]
  by_cases h1 : a₁ ∈ I₁ ∧ b₁ ∈ I₁
  · have hb₁I : b₁ ∈ I := (mem_filter.mp h1.2).1
    have ha₂_not : a₂ ∉ I₂ := fun h =>
      hI_indep (mem_coe.mpr hb₁I) (mem_coe.mpr (mem_filter.mp h).1) hne_b1a2 hH_b1a2
    have hI₂_indep : Q.IsIndepSet (I₂ : Set V) :=
      hQ_sub_part2 I₂ Subset.rfl (fun h => ha₂_not h.1)
    have h2_le : I₂.card + 1 ≤ (Q.induce { z : V | ¬ P z }).indepNum :=
      hforced₂ I₂ hI₂_nP hI₂_indep ha₂_not
    have hI₁_erase_indep : Q.IsIndepSet ((I₁.erase b₁) : Set V) :=
      hQ_sub_part1 (I₁.erase b₁) (erase_subset _ _) (fun h => (notMem_erase b₁ I₁) h.2)
    have h1_le' : (I₁.erase b₁).card + 1 ≤ (Q.induce { z : V | P z }).indepNum :=
      hforced₁ (I₁.erase b₁) (fun z hz => hI₁_P z (mem_of_mem_erase hz))
        hI₁_erase_indep (notMem_erase b₁ I₁)
    have h1_le : I₁.card ≤ (Q.induce { z : V | P z }).indepNum := by
      rwa [card_erase_add_one h1.2] at h1_le'
    omega
  · by_cases h2 : a₂ ∈ I₂ ∧ b₂ ∈ I₂
    · have ha₂I : a₂ ∈ I := (mem_filter.mp h2.1).1
      have hb₁_not : b₁ ∉ I₁ := fun h =>
        hI_indep (mem_coe.mpr (mem_filter.mp h).1) (mem_coe.mpr ha₂I) hne_b1a2 hH_b1a2
      have hI₁_indep : Q.IsIndepSet (I₁ : Set V) :=
        hQ_sub_part1 I₁ Subset.rfl (fun h => hb₁_not h.2)
      have h1_le : I₁.card + 1 ≤ (Q.induce { z : V | P z }).indepNum :=
        hforced₁ I₁ hI₁_P hI₁_indep hb₁_not
      have hI₂_erase_indep : Q.IsIndepSet ((I₂.erase a₂) : Set V) :=
        hQ_sub_part2 (I₂.erase a₂) (erase_subset _ _) (fun h => (notMem_erase a₂ I₂) h.1)
      have h2_le' : (I₂.erase a₂).card + 1 ≤ (Q.induce { z : V | ¬ P z }).indepNum :=
        hforced₂ (I₂.erase a₂) (fun z hz => hI₂_nP z (mem_of_mem_erase hz))
          hI₂_erase_indep (notMem_erase a₂ I₂)
      have h2_le : I₂.card ≤ (Q.induce { z : V | ¬ P z }).indepNum := by
        rwa [card_erase_add_one h2.1] at h2_le'
      omega
    · have hI₁_indep : Q.IsIndepSet (I₁ : Set V) := hQ_sub_part1 I₁ Subset.rfl h1
      have hI₂_indep : Q.IsIndepSet (I₂ : Set V) := hQ_sub_part2 I₂ Subset.rfl h2
      by_cases hb₁_mem : b₁ ∈ I₁
      · have ha₂_not : a₂ ∉ I₂ := fun h =>
          hI_indep (mem_coe.mpr (mem_filter.mp hb₁_mem).1)
            (mem_coe.mpr (mem_filter.mp h).1) hne_b1a2 hH_b1a2
        have h1_le := card_le_indepNum_induce_of_subset Q P hI₁_P hI₁_indep
        have h2_le : I₂.card + 1 ≤ (Q.induce { z : V | ¬ P z }).indepNum :=
          hforced₂ I₂ hI₂_nP hI₂_indep ha₂_not
        omega
      · have h1_le := hforced₁ I₁ hI₁_P hI₁_indep hb₁_mem
        have h2_le : I₂.card ≤ (Q.induce { z : V | ¬ P z }).indepNum :=
          card_le_indepNum_induce_of_subset Q (fun z => ¬ P z) hI₂_nP hI₂_indep
        omega

/-- **CONDITIONAL BOUNDARY (explicit FMS premise on `H`):**
Under `residue H ≤ H.indepNum`, the disjoint-union forced-vertex 2-switch gives
`residue Q + 1 ≤ α(Q[P]) + α(Q[¬ P])`. -/
theorem disjointUnion_forced_residue_le_of_fms
    (Q : SimpleGraph V) [DecidableRel Q.Adj] (P : V → Prop) [DecidablePred P]
    {a₁ b₁ a₂ b₂ : V}
    (hsplit : ∀ u w, Q.Adj u w → (P u ↔ P w))
    (ha₁ : P a₁) (hb₁ : P b₁) (ha₂ : ¬ P a₂) (hb₂ : ¬ P b₂)
    (he₁ : Q.Adj a₁ b₁) (he₂ : Q.Adj a₂ b₂)
    (hforced₁ : IsForcedInPart Q P b₁)
    (hforced₂ : IsForcedInPart Q (fun z => ¬ P z) a₂)
    (hFMS : SimpleGraph.residue (twoSwitch Q a₁ b₁ a₂ b₂) ≤ (twoSwitch Q a₁ b₁ a₂ b₂).indepNum) :
    SimpleGraph.residue Q + 1 ≤
      (Q.induce { z : V | P z }).indepNum + (Q.induce { z : V | ¬ P z }).indepNum := by
  obtain ⟨_, hres, hind⟩ :=
    disjointUnion_forced_twoSwitch_indepNum_le Q P hsplit ha₁ hb₁ ha₂ hb₂ he₁ he₂ hforced₁ hforced₂
  omega

end DisjointUnionTwoSwitch

end WOWII61.FirstIsolation
