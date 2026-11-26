module

public import WOWII61.PackingForest

/-!
# Terminal-Pair Packing Consequence for the Uniform `⌊(2D + 6) / 7⌋` Bound

This module formalizes the uniform `⌊(2D + 6) / 7⌋` packing bound unconditionally
from the **Terminal-Pair Property** (Theorem 1), reusing `PackingForest.lean`:

1. `TerminalPairs G T`: a finite family `T : Finset (V × V)` of disjoint terminal pairs in `G`
   such that every terminal has positive degree in `G`, endpoints of the same pair have
   `G.edist ≥ 4`, and terminals of distinct pairs have `G.edist ≥ 3`.
2. `addPairs G T`: the graph `G + T` obtained by adding the edges `{p.1, p.2}` for `p ∈ T`,
   together with the exact independent-set equivalence `addPairs_isIndepSet_iff`.
3. **Unconditional `P₅`-Block + `P₂`-Tail 3-Packing Selection**
   (`exists_threePacking_of_diametral_pairs_avoiding`,
   `card_add_two_diam_add_six_div_seven_le_largestInducedForestSize`):
   given a connected nontrivial graph `G`, a diametral geodesic `p : Fin (G.diam + 1) → V`,
   and any independent set `I` avoiding simultaneous selection of `(p (7j), p (7j + 4))`
   for all `j < ((2 * G.diam + 6) / 7) / 2`, we choose 2 outsiders per `P₅` block (separated
   by two unused spacer positions between blocks) plus 1 outsider in an optional trailing `P₂`
   block, obtaining a 3-packing `W` disjoint from `I` of cardinality `(2 * G.diam + 6) / 7`
   and hence `I.card + (2 * G.diam + 6) / 7 ≤ G.largestInducedForestSize`.
4. **Unconditional Packing Consequence of the Pair Property**
   (`uniform_diam_bound_of_pair_property`):
   if `G` satisfies the terminal-pair property (Theorem 1), then
   `SimpleGraph.residue G + (2 * G.diam + 6) / 7 ≤ G.largestInducedForestSize`.
5. **Twelve Exact Diameters for WOWII Conjecture 61**
   (`ceil_div_three_le_two_diam_add_six_div_seven_of_twelve_diams`,
   `wowii61_of_twelve_diams_of_pair_property`):
   for `G.diam ∈ {1, 2, 3, 4, 5, 6, 8, 9, 11, 12, 15, 18}`,
   `(G.diam + 2) / 3 ≤ (2 * G.diam + 6) / 7`, so the pair property implies
   `SimpleGraph.residue G + (G.diam + 2) / 3 ≤ G.largestInducedForestSize`.
-/

@[expose] public section

namespace WOWII61.PackingBound

open SimpleGraph Finset WOWII61.PackingForest

section TerminalPairs

variable {V : Type*}

/-- A finite family `T` of pairs of vertices in `G` satisfying the hypotheses of Theorem 1:
- every terminal has positive degree in `G`,
- the two ends of each pair have extended distance at least `4`,
- terminals belonging to different pairs have extended distance at least `3`
  (which in particular forces all pairs to be pairwise disjoint). -/
structure TerminalPairs [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset (V × V)) : Prop where
  pos_deg : ∀ p ∈ T, 0 < G.degree p.1 ∧ 0 < G.degree p.2
  within_pair : ∀ p ∈ T, (4 : ℕ∞) ≤ G.edist p.1 p.2
  between_pairs : ∀ p ∈ T, ∀ q ∈ T, p ≠ q →
    (3 : ℕ∞) ≤ G.edist p.1 q.1 ∧ (3 : ℕ∞) ≤ G.edist p.1 q.2 ∧
    (3 : ℕ∞) ≤ G.edist p.2 q.1 ∧ (3 : ℕ∞) ≤ G.edist p.2 q.2

/-- The graph `G + T` obtained by adding an edge between `p.1` and `p.2` for every `p ∈ T`. -/
def addPairs (G : SimpleGraph V) (T : Finset (V × V)) : SimpleGraph V :=
  G ⊔ SimpleGraph.fromEdgeSet { e : Sym2 V | ∃ p ∈ T, e = s(p.1, p.2) }

theorem TerminalPairs.ne_of_mem [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {T : Finset (V × V)}
    (hT : TerminalPairs G T) {p : V × V} (hp : p ∈ T) : p.1 ≠ p.2 := by
  intro heq
  have h4 := hT.within_pair p hp
  rw [heq, SimpleGraph.edist_self] at h4
  exact absurd h4 (by decide)

/-- Distinct terminals of a valid `TerminalPairs` family have extended distance at least `3`. -/
theorem TerminalPairs.edist_ge_three_of_terminals [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {T : Finset (V × V)}
    (hT : TerminalPairs G T) {p q : V × V} (hp : p ∈ T) (hq : q ∈ T)
    {u w : V} (hu : u = p.1 ∨ u = p.2) (hw : w = q.1 ∨ w = q.2) (huw : u ≠ w) :
    (3 : ℕ∞) ≤ G.edist u w := by
  by_cases hpq : p = q
  · subst hpq
    have h4 : (4 : ℕ∞) ≤ G.edist p.1 p.2 := hT.within_pair p hp
    have h34 : (3 : ℕ∞) ≤ 4 := by decide
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
    · exact absurd rfl huw
    · exact h34.trans h4
    · rw [SimpleGraph.edist_comm]; exact h34.trans h4
    · exact absurd rfl huw
  · obtain ⟨h11, h12, h21, h22⟩ := hT.between_pairs p hp q hq hpq
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
    · exact h11
    · exact h12
    · exact h21
    · exact h22

/-- An independent set in `G + T` is equivalently an independent set in `G` that does not
contain both endpoints of any pair `p ∈ T` (assuming no degenerate pair `p.1 = p.2`). -/
theorem addPairs_isIndepSet_iff {G : SimpleGraph V} {T : Finset (V × V)}
    (hne : ∀ p ∈ T, p.1 ≠ p.2) (I : Finset V) :
    (addPairs G T).IsIndepSet (I : Set V) ↔
      G.IsIndepSet (I : Set V) ∧ ∀ p ∈ T, ¬ (p.1 ∈ I ∧ p.2 ∈ I) := by
  constructor
  · intro hI
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab hadj
      exact hI ha hb hab (Or.inl hadj)
    · intro p hp ⟨h1, h2⟩
      have hadj : (addPairs G T).Adj p.1 p.2 :=
        Or.inr ⟨⟨p, hp, rfl⟩, hne p hp⟩
      exact hI (mem_coe.mpr h1) (mem_coe.mpr h2) (hne p hp) hadj
  · rintro ⟨hG, hT⟩ a ha b hb hab hadj
    rw [addPairs, SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj] at hadj
    rcases hadj with hGab | ⟨⟨p, hp, heq⟩, _⟩
    · exact hG ha hb hab hGab
    · rw [Sym2.eq_iff] at heq
      rw [mem_coe] at ha hb
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hT p hp ⟨ha, hb⟩
      · exact hT p hp ⟨hb, ha⟩

/-- The **Terminal-Pair Property** (conclusion of Theorem 1) for a graph `G`:
every valid family `T` of terminal pairs admits an independent set of `G` avoiding both ends
of every pair in `T` with cardinality at least `SimpleGraph.residue G`. -/
def SatisfiesTerminalPairProperty [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ T : Finset (V × V), TerminalPairs G T →
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧
      (∀ p ∈ T, ¬ (p.1 ∈ I ∧ p.2 ∈ I)) ∧
      SimpleGraph.residue G ≤ I.card

end TerminalPairs

/-! ## `P₅`-Block + `P₂`-Tail Selection Along a Diametral Geodesic -/

section DiametralBlockPacking

variable {V : Type*}

/-- Every nontrivial finite connected graph has diameter at least `1`. -/
theorem one_le_diam_of_connected [Fintype V] [Nontrivial V]
    (G : SimpleGraph V) (hconn : G.Connected) : 1 ≤ G.diam := by
  have : Nonempty V := inferInstance
  have hne_top : G.ediam ≠ ⊤ := by
    obtain ⟨u, v, huv⟩ := G.exists_edist_eq_ediam_of_finite
    rw [← huv, SimpleGraph.edist_ne_top_iff_reachable]
    exact hconn u v
  obtain ⟨u, v, huv⟩ := exists_pair_ne V
  have h1 : (1 : ℕ∞) ≤ G.edist u v :=
    Order.one_le_iff_pos.mpr (G.edist_pos_of_ne huv)
  have hle : G.edist u v ≤ G.ediam := SimpleGraph.edist_le_ediam
  have h1' : (1 : ℕ∞) ≤ G.ediam := h1.trans hle
  have hcoe : (G.diam : ℕ∞) = G.ediam := ENat.natCast_toNat hne_top
  rw [← hcoe] at h1'
  exact_mod_cast h1'

private lemma block_end_le_diam {D j : ℕ}
    (hj : j < ((2 * D + 6) / 7) / 2) : 7 * j + 4 ≤ D := by
  omega

private lemma tail_end_le_diam {D : ℕ}
    (hodd : ((2 * D + 6) / 7) % 2 = 1) :
    7 * (((2 * D + 6) / 7) / 2) + 1 ≤ D := by
  omega

/-- Index selection for Theorem 2:
for each `k < t = (2 * D + 6) / 7`, let `j = k / 2` and `h = t / 2`:
- if `j < h` (`P₅` block `[7j, 7j + 4]`):
  - if `p (7j) ∈ I`, pick `7j + 1` (even `k`) and `7j + 4` (odd `k`);
  - if `p (7j) ∉ I`, pick `7j` (even `k`) and whichever of `7j + 3, 7j + 4` is outside `I` (odd `k`);
- if `j = h` (optional trailing `P₂` block `[7h, 7h + 1]`, when `t` is odd):
  pick whichever of `7h, 7h + 1` is outside `I`. -/
private def blockPickIdx [DecidableEq V] {D : ℕ}
    (p : Fin (D + 1) → V) (I : Finset V) (k : Fin ((2 * D + 6) / 7)) : Fin (D + 1) :=
  let t := (2 * D + 6) / 7
  let h := t / 2
  let j := k.val / 2
  if hj : j < h then
    have hj4 : 7 * j + 4 ≤ D := block_end_le_diam hj
    if k.val % 2 = 0 then
      if p ⟨7 * j, by omega⟩ ∈ I then ⟨7 * j + 1, by omega⟩ else ⟨7 * j, by omega⟩
    else
      if p ⟨7 * j, by omega⟩ ∈ I then ⟨7 * j + 4, by omega⟩
      else if p ⟨7 * j + 3, by omega⟩ ∈ I then ⟨7 * j + 4, by omega⟩
      else ⟨7 * j + 3, by omega⟩
  else
    have hodd : t % 2 = 1 := by omega
    have htail : 7 * h + 1 ≤ D := tail_end_le_diam hodd
    if p ⟨7 * h, by omega⟩ ∈ I then ⟨7 * h + 1, by omega⟩ else ⟨7 * h, by omega⟩

private lemma blockPickIdx_lower [DecidableEq V] {D : ℕ}
    (p : Fin (D + 1) → V) (I : Finset V) (k : Fin ((2 * D + 6) / 7)) :
    7 * (k.val / 2) ≤ (blockPickIdx p I k).val := by
  have hk := k.isLt
  unfold blockPickIdx
  dsimp only
  split_ifs <;> dsimp only <;> omega

private lemma blockPickIdx_upper_of_lt [DecidableEq V] {D : ℕ}
    (p : Fin (D + 1) → V) (I : Finset V) (k : Fin ((2 * D + 6) / 7))
    (hj : k.val / 2 < ((2 * D + 6) / 7) / 2) :
    (blockPickIdx p I k).val ≤ 7 * (k.val / 2) + 4 := by
  unfold blockPickIdx
  dsimp only
  rw [dite_eq_left hj]
  split_ifs <;> dsimp only <;> omega

private lemma blockPickIdx_gap [DecidableEq V] {D : ℕ}
    (p : Fin (D + 1) → V) (I : Finset V)
    {a b : Fin ((2 * D + 6) / 7)} (hab : a.val < b.val) :
    (blockPickIdx p I a).val + 3 ≤ (blockPickIdx p I b).val := by
  by_cases hdiv : a.val / 2 = b.val / 2
  · have hja : a.val / 2 < ((2 * D + 6) / 7) / 2 := by
      have ha_lt := a.isLt
      have hb_lt := b.isLt
      omega
    have hjb : b.val / 2 < ((2 * D + 6) / 7) / 2 := hdiv ▸ hja
    have ha_mod : a.val % 2 = 0 := by omega
    have hb_mod : b.val % 2 = 1 := by omega
    have hj4 : 7 * (a.val / 2) + 4 ≤ D := block_end_le_diam hja
    have hpt_eq : (⟨7 * (a.val / 2), by omega⟩ : Fin (D + 1)) =
        ⟨7 * (b.val / 2), by omega⟩ := Fin.ext (by dsimp only; omega)
    unfold blockPickIdx
    dsimp only
    rw [dite_eq_left hja, dite_eq_left hjb, ite_eq_left ha_mod, ite_eq_right (by omega : ¬ b.val % 2 = 0)]
    rw [← hpt_eq]
    by_cases hmem : p ⟨7 * (a.val / 2), by omega⟩ ∈ I
    · rw [ite_eq_left hmem, ite_eq_left hmem]
      dsimp only
      omega
    · rw [ite_eq_right hmem, ite_eq_right hmem]
      split_ifs <;> dsimp only <;> omega
  · have hlt_div : a.val / 2 < b.val / 2 := by omega
    have hja : a.val / 2 < ((2 * D + 6) / 7) / 2 := by
      have hb_lt := b.isLt
      omega
    have hup := blockPickIdx_upper_of_lt p I a hja
    have hlo := blockPickIdx_lower p I b
    omega

private lemma blockPickIdx_not_mem [DecidableEq V] {D : ℕ}
    (G : SimpleGraph V) (p : Fin (D + 1) → V)
    (hp_adj : ∀ i : Fin D, G.Adj (p i.castSucc) (p i.succ))
    {I : Finset V} (hI : G.IsIndepSet (I : Set V))
    (hI_pairs : ∀ j : Fin (((2 * D + 6) / 7) / 2),
      ¬ (p ⟨7 * j.val, by have := block_end_le_diam j.isLt; omega⟩ ∈ I ∧
         p ⟨7 * j.val + 4, by have := block_end_le_diam j.isLt; omega⟩ ∈ I))
    (k : Fin ((2 * D + 6) / 7)) :
    p (blockPickIdx p I k) ∉ I := by
  unfold blockPickIdx
  dsimp only
  split_ifs with hj hmod hmem0 hmem0' hmem3 htailmem
  · -- `j < h`, `k % 2 = 0`, `p (7j) ∈ I` -> pick `7j + 1`
    have hj4 : 7 * (k.val / 2) + 4 ≤ D := block_end_le_diam hj
    have hadj : G.Adj (p ⟨7 * (k.val / 2), by omega⟩) (p ⟨7 * (k.val / 2) + 1, by omega⟩) :=
      hp_adj ⟨7 * (k.val / 2), by omega⟩
    exact fun h1 => hI (mem_coe.mpr hmem0) (mem_coe.mpr h1) hadj.ne hadj
  · -- `j < h`, `k % 2 = 0`, `p (7j) ∉ I` -> pick `7j`
    exact hmem0
  · -- `j < h`, `k % 2 = 1`, `p (7j) ∈ I` -> pick `7j + 4`
    exact fun h4 => hI_pairs ⟨k.val / 2, hj⟩ ⟨hmem0', h4⟩
  · -- `j < h`, `k % 2 = 1`, `p (7j) ∉ I`, `p (7j + 3) ∈ I` -> pick `7j + 4`
    have hj4 : 7 * (k.val / 2) + 4 ≤ D := block_end_le_diam hj
    have hadj : G.Adj (p ⟨7 * (k.val / 2) + 3, by omega⟩) (p ⟨7 * (k.val / 2) + 4, by omega⟩) :=
      hp_adj ⟨7 * (k.val / 2) + 3, by omega⟩
    exact fun h4 => hI (mem_coe.mpr hmem3) (mem_coe.mpr h4) hadj.ne hadj
  · -- `j < h`, `k % 2 = 1`, `p (7j) ∉ I`, `p (7j + 3) ∉ I` -> pick `7j + 3`
    exact hmem3
  · -- `j = h`, trailing `P₂`, `p (7h) ∈ I` -> pick `7h + 1`
    have hodd : ((2 * D + 6) / 7) % 2 = 1 := by omega
    have htail : 7 * (((2 * D + 6) / 7) / 2) + 1 ≤ D := tail_end_le_diam hodd
    have hadj : G.Adj (p ⟨7 * (((2 * D + 6) / 7) / 2), by omega⟩)
        (p ⟨7 * (((2 * D + 6) / 7) / 2) + 1, by omega⟩) :=
      hp_adj ⟨7 * (((2 * D + 6) / 7) / 2), by omega⟩
    exact fun h1 => hI (mem_coe.mpr htailmem) (mem_coe.mpr h1) hadj.ne hadj
  · -- `j = h`, trailing `P₂`, `p (7h) ∉ I` -> pick `7h`
    exact htailmem

/--
**Unconditional `P₅`-Block + `P₂`-Tail 3-Packing Construction:**
Given a diametral geodesic `p` of a finite connected graph `G` (`D = G.diam`)
and an independent set `I` omitting at least one endpoint of each `P₅` block `(p (7j), p (7j + 4))`,
there is a 3-packing `W` of size `(2 * D + 6) / 7` disjoint from `I`.
(Note: for `D = 0`, `(2 * 0 + 6) / 7 = 0`, so `W = ∅` works automatically as well!)
-/
theorem exists_threePacking_of_diametral_pairs_avoiding [DecidableEq V]
    {D : ℕ} (G : SimpleGraph V) (p : Fin (D + 1) → V)
    (hp_adj : ∀ i : Fin D, G.Adj (p i.castSucc) (p i.succ))
    (hp_edist : ∀ i j : Fin (D + 1), i.val ≤ j.val →
      G.edist (p i) (p j) = ((j.val - i.val : ℕ) : ℕ∞))
    {I : Finset V} (hI : G.IsIndepSet (I : Set V))
    (hI_pairs : ∀ j : Fin (((2 * D + 6) / 7) / 2),
      ¬ (p ⟨7 * j.val, by have := block_end_le_diam j.isLt; omega⟩ ∈ I ∧
         p ⟨7 * j.val + 4, by have := block_end_le_diam j.isLt; omega⟩ ∈ I)) :
    ∃ W : Finset V,
      IsThreePacking G W ∧ Disjoint I W ∧ W.card = (2 * D + 6) / 7 := by
  let f : Fin ((2 * D + 6) / 7) → V := fun k => p (blockPickIdx p I k)
  have hf_edist : ∀ a b : Fin ((2 * D + 6) / 7), a ≠ b → (3 : ℕ∞) ≤ G.edist (f a) (f b) := by
    intro a b hab
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hgt
    · have hgap := blockPickIdx_gap p I hlt
      rw [hp_edist _ _ (by omega)]
      exact_mod_cast (by omega : 3 ≤ (blockPickIdx p I b).val - (blockPickIdx p I a).val)
    · have hgap := blockPickIdx_gap p I hgt
      rw [SimpleGraph.edist_comm, hp_edist _ _ (by omega)]
      exact_mod_cast (by omega : 3 ≤ (blockPickIdx p I a).val - (blockPickIdx p I b).val)
  have hf_inj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have h3 := hf_edist a b hne
    rw [hab, SimpleGraph.edist_self] at h3
    exact absurd h3 (by decide)
  let W : Finset V := Finset.univ.image f
  refine ⟨W, ?_, ?_, ?_⟩
  · intro u hu w hw huw
    rcases mem_image.mp hu with ⟨a, _, rfl⟩
    rcases mem_image.mp hw with ⟨b, _, rfl⟩
    exact hf_edist a b (fun h => huw (congrArg f h))
  · rw [Finset.disjoint_right]
    intro u hu
    rcases mem_image.mp hu with ⟨k, _, rfl⟩
    exact blockPickIdx_not_mem G p hp_adj hI hI_pairs k
  · rw [card_image_of_injective _ hf_inj, card_fin]

/-- **Unconditional Forest Bound from Pair-Avoiding Independent Set:**
any independent set `I` avoiding both endpoints of every `P₅` block along a diametral geodesic
gives `I.card + (2 * G.diam + 6) / 7 ≤ G.largestInducedForestSize`. -/
theorem card_add_two_diam_add_six_div_seven_le_largestInducedForestSize
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (p : Fin (G.diam + 1) → V)
    (hp_adj : ∀ i : Fin G.diam, G.Adj (p i.castSucc) (p i.succ))
    (hp_edist : ∀ i j : Fin (G.diam + 1), i.val ≤ j.val →
      G.edist (p i) (p j) = ((j.val - i.val : ℕ) : ℕ∞))
    {I : Finset V} (hI : G.IsIndepSet (I : Set V))
    (hI_pairs : ∀ j : Fin (((2 * G.diam + 6) / 7) / 2),
      ¬ (p ⟨7 * j.val, by have := block_end_le_diam j.isLt; omega⟩ ∈ I ∧
         p ⟨7 * j.val + 4, by have := block_end_le_diam j.isLt; omega⟩ ∈ I)) :
    I.card + (2 * G.diam + 6) / 7 ≤ G.largestInducedForestSize := by
  obtain ⟨W, hW_pack, hdisj, hW_card⟩ :=
    exists_threePacking_of_diametral_pairs_avoiding G p hp_adj hp_edist hI hI_pairs
  have hbound := card_indep_add_threePacking_le_largestInducedForestSize G hI hW_pack hdisj
  rwa [hW_card] at hbound

/-- The explicit family of `P₅`-block endpoint pairs `(p (7j), p (7j + 4))` along a diametral
geodesic satisfies `TerminalPairs G T`. -/
theorem diametral_pairs_valid [Fintype V] [DecidableEq V]
    {D : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (p : Fin (D + 1) → V)
    (hp_adj : ∀ i : Fin D, G.Adj (p i.castSucc) (p i.succ))
    (hp_edist : ∀ i j : Fin (D + 1), i.val ≤ j.val →
      G.edist (p i) (p j) = ((j.val - i.val : ℕ) : ℕ∞)) :
    let h := ((2 * D + 6) / 7) / 2
    let pairOf : Fin h → V × V := fun j =>
      (p ⟨7 * j.val, by have := block_end_le_diam j.isLt; omega⟩,
       p ⟨7 * j.val + 4, by have := block_end_le_diam j.isLt; omega⟩)
    TerminalPairs G (Finset.univ.image pairOf) := by
  intro h pairOf
  have edist_ge_of_abs : ∀ (a b : Fin (D + 1)) (m : ℕ),
      (a.val + m ≤ b.val ∨ b.val + m ≤ a.val) → (m : ℕ∞) ≤ G.edist (p a) (p b) := by
    intro a b m hsep
    rcases hsep with h1 | h2
    · rw [hp_edist a b (by omega)]
      exact_mod_cast (by omega : m ≤ b.val - a.val)
    · rw [SimpleGraph.edist_comm, hp_edist b a (by omega)]
      exact_mod_cast (by omega : m ≤ a.val - b.val)
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    rcases mem_image.mp hq with ⟨j, _, rfl⟩
    have hj4 : 7 * j.val + 4 ≤ D := block_end_le_diam j.isLt
    have hadj1 : G.Adj (p ⟨7 * j.val, by omega⟩) (p ⟨7 * j.val + 1, by omega⟩) :=
      hp_adj ⟨7 * j.val, by omega⟩
    have hadj2 : G.Adj (p ⟨7 * j.val + 4, by omega⟩) (p ⟨7 * j.val + 3, by omega⟩) :=
      (hp_adj ⟨7 * j.val + 3, by omega⟩).symm
    exact ⟨Finset.card_pos.mpr ⟨_, (G.mem_neighborFinset _ _).mpr hadj1⟩,
           Finset.card_pos.mpr ⟨_, (G.mem_neighborFinset _ _).mpr hadj2⟩⟩
  · intro q hq
    rcases mem_image.mp hq with ⟨j, _, rfl⟩
    exact edist_ge_of_abs _ _ 4 (Or.inl (by dsimp only; omega))
  · intro q₁ hq₁ q₂ hq₂ hne
    rcases mem_image.mp hq₁ with ⟨j₁, _, rfl⟩
    rcases mem_image.mp hq₂ with ⟨j₂, _, rfl⟩
    have hjne : j₁ ≠ j₂ := fun heq => hne (congrArg pairOf heq)
    have hval : j₁.val < j₂.val ∨ j₂.val < j₁.val := lt_or_gt_of_ne (Fin.val_ne_of_ne hjne)
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact edist_ge_of_abs _ _ 3 (by rcases hval with hlt | hgt <;> [left; right] <;> dsimp only <;> omega)
    · exact edist_ge_of_abs _ _ 3 (by rcases hval with hlt | hgt <;> [left; right] <;> dsimp only <;> omega)
    · exact edist_ge_of_abs _ _ 3 (by rcases hval with hlt | hgt <;> [left; right] <;> dsimp only <;> omega)
    · exact edist_ge_of_abs _ _ 3 (by rcases hval with hlt | hgt <;> [left; right] <;> dsimp only <;> omega)

/--
**Theorem 2 (Unconditional Packing Consequence of the Terminal-Pair Property):**
For every finite connected graph `G` (on at least one vertex, hence including all nontrivial
connected graphs), if `G` satisfies `SatisfiesTerminalPairProperty G`, then
`SimpleGraph.residue G + (2 * G.diam + 6) / 7 ≤ G.largestInducedForestSize`.
(Note: even for `D = 0`, `(2 * 0 + 6) / 7 = 0`, so the bound holds for `[Nonempty V]` as well!)
-/
theorem uniform_diam_bound_of_pair_property
    [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hPair : SatisfiesTerminalPairProperty G) :
    SimpleGraph.residue G + (2 * G.diam + 6) / 7 ≤ G.largestInducedForestSize := by
  obtain ⟨p, hp_adj, _, hp_edist⟩ := exists_diametral_geodesic G hconn
  let h := ((2 * G.diam + 6) / 7) / 2
  let pairOf : Fin h → V × V := fun j =>
    (p ⟨7 * j.val, by have := block_end_le_diam j.isLt; omega⟩,
     p ⟨7 * j.val + 4, by have := block_end_le_diam j.isLt; omega⟩)
  let T : Finset (V × V) := Finset.univ.image pairOf
  have hT : TerminalPairs G T := diametral_pairs_valid G p hp_adj hp_edist
  obtain ⟨I, hI_indep, hI_avoid, hI_card⟩ := hPair T hT
  have hI_pairs : ∀ j : Fin h,
      ¬ (p ⟨7 * j.val, by have := block_end_le_diam j.isLt; omega⟩ ∈ I ∧
         p ⟨7 * j.val + 4, by have := block_end_le_diam j.isLt; omega⟩ ∈ I) := by
    intro j
    exact hI_avoid (pairOf j) (mem_image.mpr ⟨j, mem_univ j, rfl⟩)
  have hbound :=
    card_add_two_diam_add_six_div_seven_le_largestInducedForestSize
      G p hp_adj hp_edist hI_indep hI_pairs
  omega

/-- Arithmetic comparison for the twelve exact diameters where `⌊(2D + 6) / 7⌋` attains `⌈D / 3⌉`:
`D ∈ {1, 2, 3, 4, 5, 6, 8, 9, 11, 12, 15, 18}`. -/
theorem ceil_div_three_eq_two_diam_add_six_div_seven_of_twelve_diams {D : ℕ}
    (hD : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨
          D = 8 ∨ D = 9 ∨ D = 11 ∨ D = 12 ∨ D = 15 ∨ D = 18) :
    (D + 2) / 3 = (2 * D + 6) / 7 := by
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **Corollary (12 Exact Diameters for WOWII #61 from the Pair Property):**
for `G.diam ∈ {1, 2, 3, 4, 5, 6, 8, 9, 11, 12, 15, 18}`, `SatisfiesTerminalPairProperty G`
unconditionally implies `SimpleGraph.residue G + (G.diam + 2) / 3 ≤ G.largestInducedForestSize`. -/
theorem wowii61_of_twelve_diams_of_pair_property
    [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hD : G.diam = 1 ∨ G.diam = 2 ∨ G.diam = 3 ∨ G.diam = 4 ∨ G.diam = 5 ∨ G.diam = 6 ∨
          G.diam = 8 ∨ G.diam = 9 ∨ G.diam = 11 ∨ G.diam = 12 ∨ G.diam = 15 ∨ G.diam = 18)
    (hPair : SatisfiesTerminalPairProperty G) :
    SimpleGraph.residue G + (G.diam + 2) / 3 ≤ G.largestInducedForestSize := by
  rw [ceil_div_three_eq_two_diam_add_six_div_seven_of_twelve_diams hD]
  exact uniform_diam_bound_of_pair_property G hconn hPair

end DiametralBlockPacking

end WOWII61.PackingBound
