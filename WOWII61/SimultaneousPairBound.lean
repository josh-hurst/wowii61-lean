module

public import WOWII61.FirstIsolationSwitch
public import WOWII61.PackingForest
public import WOWII61.TerminalPairPacking

/-!
# Simultaneous Additional Edges (Theorem 1) and Uniform `⌊(2D + 6) / 7⌋` Bound (Theorem 2)

This module formalizes the simultaneous additional-edges theorem and uniform bound, reusing both
`FirstIsolationSwitch.lean` (`twoSwitch`, `firstIsolation_switch`, degree/residue invariance)
and `TerminalPairPacking.lean` (`TerminalPairs`, `uniform_diam_bound_of_pair_property`):

1. **Explicit Published Literature Premise (`MaxDegDeletionResiduePremise`):**
   universally quantified, noncircular statement of the published Maxine / Havel–Hakimi
   positive maximum-degree deletion bound (Griggs–Kleitman 1994; Favaron–Mahéo–Saclé 1991):
   for every `n : ℕ`, every simple graph `Q` on `Fin n`, and every maximum-degree vertex `v`
   of `Q` with `0 < Q.degree v`,
   `SimpleGraph.residue Q ≤ SimpleGraph.residue (Q.induce { u : Fin n | u ≠ v })`.
2. **Isomorphism Invariance & Base Case for `SimpleGraph.residue`:**
   `residue_eq_of_iso`, `MaxDegDeletionResiduePremise.apply` (lifting from `Fin n` to any
   finite type `V`), and `residue_eq_card_of_all_deg_zero`.
3. **Distance Preservation Under Vertex Deletion & Pendant-Edge 2-Switch:**
   `edist_le_induce_edist` and `edist_le_twoSwitch_induce_edist` (proving that in `H - v`,
   where `x` becomes a pendant leaf attached only to `y`, no path between vertices `≠ x`
   can visit `x`, hence distances in `H - v` between remaining terminals are `≥` those in `G`).
4. **Theorem 1 (`simultaneous_additional_edges_of_maxDegDeletion`,
   `residue_le_indepNum_addPairs_of_maxDegDeletion`):**
   full induction on graph order establishing `SatisfiesTerminalPairProperty G` (and
   `SimpleGraph.residue G ≤ (addPairs G T).indepNum`) from `MaxDegDeletionResiduePremise`.
   Also yields the Favaron–Mahéo–Saclé bound `R(G) ≤ α(G)` (`residue_le_indepNum_of_maxDegDeletion`)
   and the single-pair distance-4 corollary (`exists_indepSet_avoiding_single_pair_of_maxDegDeletion`).
5. **Theorem 2 (`uniform_diam_bound_of_maxDegDeletion`) & 12-Diameter Corollary:**
   for every nonempty finite connected graph `G` (in particular every connected graph on at
   least two vertices), assuming `MaxDegDeletionResiduePremise`,
   `SimpleGraph.residue G + (2 * G.diam + 6) / 7 ≤ G.largestInducedForestSize`,
   yielding WOWII Conjecture 61 (`SimpleGraph.residue G + (G.diam + 2) / 3 ≤ G.largestInducedForestSize`)
   for all twelve exact diameters `G.diam ∈ {1, 2, 3, 4, 5, 6, 8, 9, 11, 12, 15, 18}`.
-/

@[expose] public section

namespace WOWII61.PackingBound

open SimpleGraph Finset WOWII61.FirstIsolation WOWII61.PackingForest

/-! ## 1. Explicit Published Maxine / FMS Positive Max-Degree Deletion Premise -/

/--
**CONDITIONAL BOUNDARY (Published Maxine / Havel–Hakimi Positive Max-Degree Deletion Bound):**
For every `n : ℕ`, every simple graph `Q` on `Fin n`, and every vertex `v : Fin n` of
maximum positive degree in `Q`, deleting `v` does not decrease the Havel–Hakimi residue:
`SimpleGraph.residue Q ≤ SimpleGraph.residue (Q.induce { u : Fin n | u ≠ v })`.

This encapsulates the published Maxine bound (Griggs–Kleitman 1994; Favaron–Mahéo–Saclé 1991,
Theorem 1.2 in `arXiv:1910.06201`) as an explicit, universally quantified, noncircular
theorem premise with no extra logical assumptions.
-/
def MaxDegDeletionResiduePremise : Prop :=
  ∀ (n : ℕ) (Q : SimpleGraph (Fin n)) [DecidableRel Q.Adj] (v : Fin n),
    (∀ u, Q.degree u ≤ Q.degree v) → 0 < Q.degree v →
    SimpleGraph.residue Q ≤
      SimpleGraph.residue (Q.induce { u : Fin n | u ≠ v })

section ResidueInvariance

theorem residue_eq_of_decidableRel {V : Type*} [Fintype V]
    (G : SimpleGraph V) (inst₁ inst₂ : DecidableRel G.Adj) :
    @SimpleGraph.residue V _ G inst₁ = @SimpleGraph.residue V _ G inst₂ := by
  rw [Subsingleton.elim inst₁ inst₂]

/-- Graph isomorphisms preserve vertex degrees pointwise. -/
theorem iso_degree_eq {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) (v : V) : H.degree (e v) = G.degree v := by
  have hnb : H.neighborFinset (e v) = (G.neighborFinset v).map e.toEquiv.toEmbedding := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, mem_map, Equiv.toEmbedding_apply]
    constructor
    · intro hw
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      have : H.Adj (e v) (e (e.symm w)) := by simpa using hw
      exact e.map_rel_iff.mp this
    · rintro ⟨u, hu, rfl⟩
      exact e.map_rel_iff.mpr hu
  simp only [SimpleGraph.degree, hnb, card_map]

/-- Graph isomorphisms preserve `SimpleGraph.residue`. -/
theorem residue_eq_of_iso {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) : SimpleGraph.residue G = SimpleGraph.residue H := by
  unfold SimpleGraph.residue
  have hmap : Finset.univ.val.map (fun w : W => H.degree w) =
      Finset.univ.val.map (fun v : V => G.degree v) := by
    have huniv : Finset.univ.map e.toEquiv.toEmbedding = (Finset.univ : Finset W) := by
      ext w
      simp only [mem_map, mem_univ, true_and, Equiv.toEmbedding_apply, iff_true]
      exact ⟨e.symm w, e.apply_symm_apply w⟩
    have hval : (Finset.univ : Finset W).val = (Finset.univ : Finset V).val.map e.toEquiv := by
      rw [← huniv, Finset.map_val]
      rfl
    rw [hval, Multiset.map_map]
    congr 1
    funext v
    exact iso_degree_eq e v
  rw [hmap]

/-- Lift `MaxDegDeletionResiduePremise` from `Fin n` to any finite type `V` via `Fintype.equivFin`. -/
theorem MaxDegDeletionResiduePremise.apply {V : Type*} [Fintype V] [DecidableEq V]
    (hDel : MaxDegDeletionResiduePremise)
    (Q : SimpleGraph V) [DecidableRel Q.Adj] (v : V)
    (hmax : ∀ u, Q.degree u ≤ Q.degree v) (hpos : 0 < Q.degree v) :
    SimpleGraph.residue Q ≤ SimpleGraph.residue (Q.induce { u : V | u ≠ v }) := by
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let Q_fin : SimpleGraph (Fin (Fintype.card V)) := Q.comap e.symm
  let _ : DecidableRel Q_fin.Adj := fun a b =>
    decidable_of_iff (Q.Adj (e.symm a) (e.symm b)) Iff.rfl
  let iso : Q ≃g Q_fin :=
    { toEquiv := e
      map_rel_iff' := by
        intro a b
        change Q.Adj (e.symm (e a)) (e.symm (e b)) ↔ Q.Adj a b
        simp }
  let e_sub : { u : V // u ≠ v } ≃ { u : Fin (Fintype.card V) // u ≠ e v } :=
    { toFun := fun u => ⟨e u.1, fun h => u.2 (e.injective h)⟩
      invFun := fun u => ⟨e.symm u.1, fun h => u.2 (by simpa using congrArg e h)⟩
      left_inv := fun u => Subtype.ext (e.symm_apply_apply u.1)
      right_inv := fun u => Subtype.ext (e.apply_symm_apply u.1) }
  let iso_sub : Q.induce { u : V | u ≠ v } ≃g Q_fin.induce { u : Fin (Fintype.card V) | u ≠ e v } :=
    { toEquiv := e_sub
      map_rel_iff' := by
        intro a b
        change Q.Adj (e.symm (e a.1)) (e.symm (e b.1)) ↔ Q.Adj a.1 b.1
        simp }
  have hdeg_v : Q_fin.degree (e v) = Q.degree v := iso_degree_eq iso v
  have hmax_fin : ∀ u, Q_fin.degree u ≤ Q_fin.degree (e v) := by
    intro u
    have h1 : Q_fin.degree u = Q.degree (e.symm u) := by
      have h := iso_degree_eq iso (e.symm u)
      change Q_fin.degree (e (e.symm u)) = Q.degree (e.symm u) at h
      rwa [e.apply_symm_apply] at h
    rw [h1, hdeg_v]
    exact hmax (e.symm u)
  have hpos_fin : 0 < Q_fin.degree (e v) := by
    rw [hdeg_v]
    exact hpos
  have h1 := residue_eq_of_iso iso
  have h2 := residue_eq_of_iso iso_sub
  rw [h1, h2]
  exact hDel (Fintype.card V) Q_fin (e v) hmax_fin hpos_fin

/-- Unconditional base case: an edgeless graph (all degrees `0`) has `residue G = Fintype.card V`. -/
theorem residue_eq_card_of_all_deg_zero {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h0 : ∀ u : V, G.degree u = 0) :
    SimpleGraph.residue G = Fintype.card V := by
  unfold SimpleGraph.residue
  set l : List ℕ := (Finset.univ.val.map fun v => G.degree v).sort (· ≥ ·)
  have hlen : l.length = Fintype.card V := by
    simp [l, Multiset.length_sort]
  have hall : ∀ d ∈ l, d = 0 := by
    intro d hd
    have hmem : d ∈ Finset.univ.val.map (fun v => G.degree v) :=
      (Multiset.mem_sort (r := (· ≥ ·))).mp hd
    rcases Multiset.mem_map.mp hmem with ⟨v, _, rfl⟩
    exact h0 v
  cases hl : l with
  | nil =>
    rw [hl] at hlen
    simpa [SimpleGraph.residueAux] using hlen
  | cons d s =>
    have hd0 : d = 0 := hall d (by simp [hl])
    subst hd0
    rw [hl] at hlen
    simp only [SimpleGraph.residueAux, List.length_cons] at hlen ⊢
    omega

end ResidueInvariance

/-! ## 2. Distance Preservation Under Vertex Deletion and Pendant-Edge 2-Switch -/

section DistancePreservation

variable {V : Type*}

/-- Deleting vertices cannot shorten extended distances: `G.edist a b ≤ (G.induce S).edist a b`. -/
theorem edist_le_induce_edist (G : SimpleGraph V) (S : Set V) (a b : S) :
    G.edist a.1 b.1 ≤ (G.induce S).edist a b := by
  by_cases htop : (G.induce S).edist a b = ⊤
  · rw [htop]; exact le_top
  · obtain ⟨w, hw⟩ := (G.induce S).exists_walk_of_edist_ne_top htop
    rw [← hw]
    have hle := G.edist_le (w.map (SimpleGraph.Embedding.induce S).toHom)
    rw [SimpleGraph.Walk.length_map] at hle
    exact hle

/-- After switching `vx, wy` to `vw, xy` when `x` had sole neighbor `v`, vertex `x` has
sole neighbor `y` in `twoSwitch G v x y w`. -/
theorem twoSwitch_sole_neighbor_x (G : SimpleGraph V) {v x y w : V}
    (hsole : ∀ u, G.Adj x u ↔ u = v) (hyw : G.Adj y w)
    (hvw : ¬ G.Adj v w) (hne_vw : v ≠ w) (hne_xy : x ≠ y) (u : V) :
    (twoSwitch G v x y w).Adj x u ↔ u = y := by
  obtain ⟨_, _, hvx_ne, _, _, _, hxw_ne, _⟩ :=
    firstIsolation_distinct G hsole hyw hvw hne_vw hne_xy
  rw [twoSwitch_adj_iff G hne_vw hne_xy]
  constructor
  · rintro (⟨hG, h1, _⟩ | h2 | h3)
    · have huv : u = v := (hsole u).mp hG
      subst huv
      exact absurd Sym2.eq_swap h1
    · rw [Sym2.eq_iff] at h2
      rcases h2 with ⟨hxv, _⟩ | ⟨hxw, _⟩
      · exact absurd hxv.symm hvx_ne
      · exact absurd hxw hxw_ne
    · rw [Sym2.eq_iff] at h3
      rcases h3 with ⟨_, rfl⟩ | ⟨hxy', _⟩
      · rfl
      · exact absurd hxy' hne_xy
  · rintro rfl
    exact Or.inr (Or.inr rfl)

private lemma exists_walk_G_of_twoSwitch_induce_path (G : SimpleGraph V) {v x y w : V}
    (hsole : ∀ u, G.Adj x u ↔ u = v) (hyw : G.Adj y w)
    (hvw : ¬ G.Adj v w) (hne_vw : v ≠ w) (hne_xy : x ≠ y)
    {a b : { u : V // u ≠ v }}
    (π : ((twoSwitch G v x y w).induce { u : V | u ≠ v }).Walk a b)
    (hπ : π.IsPath) (ha : a.1 ≠ x) (hb : b.1 ≠ x) :
    ∃ wG : G.Walk a.1 b.1, wG.length = π.length := by
  have hsole_H : ∀ u, (twoSwitch G v x y w).Adj x u ↔ u = y :=
    twoSwitch_sole_neighbor_x G hsole hyw hvw hne_vw hne_xy
  induction π with
  | nil =>
    exact ⟨.nil, rfl⟩
  | @cons a c b hac rest ih =>
    have hc : c.1 ≠ x := by
      intro hcx
      cases rest with
      | nil => exact hb hcx
      | @cons _ d _ hcd rest' =>
        have ha_adj : (twoSwitch G v x y w).Adj x a.1 := by
          have h' : (twoSwitch G v x y w).Adj c.1 a.1 := hac.symm
          rwa [hcx] at h'
        have hd_adj : (twoSwitch G v x y w).Adj x d.1 := by
          have h' : (twoSwitch G v x y w).Adj c.1 d.1 := hcd
          rwa [hcx] at h'
        have hay : a.1 = y := (hsole_H a.1).mp ha_adj
        have hdy : d.1 = y := (hsole_H d.1).mp hd_adj
        have had : a = d := Subtype.ext (hay.trans hdy.symm)
        have hnodup := hπ.support_nodup
        simp only [Walk.support_cons, List.nodup_cons, List.mem_cons, not_or] at hnodup
        exact hnodup.1.2 (had ▸ rest'.start_mem_support)
    have hacG : G.Adj a.1 c.1 := by
      have hH : (twoSwitch G v x y w).Adj a.1 c.1 := hac
      rw [twoSwitch_adj_iff G hne_vw hne_xy] at hH
      rcases hH with ⟨hG, _, _⟩ | hvw' | hxy'
      · exact hG
      · rw [Sym2.eq_iff] at hvw'
        rcases hvw' with ⟨hav, _⟩ | ⟨_, hcv⟩
        · exact absurd hav a.2
        · exact absurd hcv c.2
      · rw [Sym2.eq_iff] at hxy'
        rcases hxy' with ⟨hax, _⟩ | ⟨_, hcx⟩
        · exact absurd hax ha
        · exact absurd hcx hc
    obtain ⟨wRest, hwRest⟩ := ih hπ.of_cons hc hb
    exact ⟨.cons hacG wRest, by simp [hwRest]⟩

/-- **Pendant-Edge Distance Preservation:**
In `H - v` where `H = twoSwitch G v x y w` and `x` had sole neighbor `v` in `G`, the added
edge `xy` is a pendant edge at `x`, so no simple path between vertices `≠ x` can traverse `x`.
Hence for all `a, b ≠ v` with `a, b ≠ x`, `G.edist a b ≤ (H - v).edist a b`. -/
theorem edist_le_twoSwitch_induce_edist [DecidableEq V] (G : SimpleGraph V) {v x y w : V}
    (hsole : ∀ u, G.Adj x u ↔ u = v) (hyw : G.Adj y w)
    (hvw : ¬ G.Adj v w) (hne_vw : v ≠ w) (hne_xy : x ≠ y)
    (a b : { u : V // u ≠ v }) (ha : a.1 ≠ x) (hb : b.1 ≠ x) :
    G.edist a.1 b.1 ≤ ((twoSwitch G v x y w).induce { u : V | u ≠ v }).edist a b := by
  let H' := (twoSwitch G v x y w).induce { u : V | u ≠ v }
  by_cases htop : H'.edist a b = ⊤
  · rw [htop]; exact le_top
  · obtain ⟨walk, hwalk⟩ := H'.exists_walk_of_edist_ne_top htop
    have hpath : walk.bypass.IsPath := walk.bypass_isPath
    obtain ⟨wG, hwG⟩ :=
      exists_walk_G_of_twoSwitch_induce_path G hsole hyw hvw hne_vw hne_xy walk.bypass hpath ha hb
    have hle1 : G.edist a.1 b.1 ≤ (wG.length : ℕ∞) := G.edist_le wG
    have hle2 : (walk.bypass.length : ℕ∞) ≤ (walk.length : ℕ∞) :=
      Nat.cast_le.mpr walk.length_bypass_le_length
    calc
      G.edist a.1 b.1 ≤ (wG.length : ℕ∞) := hle1
      _ = (walk.bypass.length : ℕ∞) := by rw [hwG]
      _ ≤ (walk.length : ℕ∞) := hle2
      _ = H'.edist a b := hwalk

end DistancePreservation

/-! ## 3. Theorem 1: Simultaneous Additional Edges (Induction on Graph Order) -/

section SimultaneousAdditionalEdges

private lemma card_subtype_ne {V : Type*} [Fintype V] [DecidableEq V] (v : V) :
    Fintype.card { u : V // u ≠ v } + 1 = Fintype.card V := by
  have h := Fintype.card_subtype_compl (fun u : V => u = v)
  have h1 : Fintype.card { u : V // u = v } = 1 := Fintype.card_unique
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  change Fintype.card { u : V // ¬ u = v } + 1 = Fintype.card V
  omega

private lemma sole_neighbor_of_induce_deg_zero {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v x : V} (hxv : x ≠ v)
    (hpos : 0 < G.degree x)
    (hzero : (G.induce { u : V | u ≠ v }).degree ⟨x, hxv⟩ = 0) :
    ∀ u : V, G.Adj x u ↔ u = v := by
  have hno_other : ∀ u : V, u ≠ v → ¬ G.Adj x u := by
    intro u huv hadj
    have hmem : (⟨u, huv⟩ : { z : V // z ≠ v }) ∈
        (G.induce { z : V | z ≠ v }).neighborFinset ⟨x, hxv⟩ := by
      simpa [SimpleGraph.mem_neighborFinset] using hadj
    have hpos' : 0 < (G.induce { z : V | z ≠ v }).degree ⟨x, hxv⟩ :=
      Finset.card_pos.mpr ⟨⟨u, huv⟩, hmem⟩
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  have hxz : G.Adj x z := (G.mem_neighborFinset x z).mp hz
  have hzv : z = v := by
    by_contra hne
    exact hno_other z hne hxz
  have hxv_adj : G.Adj x v := hzv ▸ hxz
  intro u
  constructor
  · intro hadj
    by_contra huv
    exact hno_other u huv hadj
  · rintro rfl
    exact hxv_adj

private lemma edist_ge_four_implies_switch_conds {V : Type*} (G : SimpleGraph V) {v x y w : V}
    (hvx : G.Adj v x) (hyw : G.Adj y w) (h4 : (4 : ℕ∞) ≤ G.edist x y) :
    ¬ G.Adj v w ∧ ¬ G.Adj x y ∧ v ≠ w ∧ x ≠ y := by
  have hne_xy : x ≠ y := by
    intro h; rw [h, SimpleGraph.edist_self] at h4; exact absurd h4 (by decide)
  have hxy : ¬ G.Adj x y := by
    intro h
    rw [SimpleGraph.edist_eq_one_iff_adj.mpr h] at h4
    exact absurd h4 (by decide)
  have hne_vw : v ≠ w := by
    intro h
    subst h
    have hle : G.edist x y ≤ 2 := by
      calc
        G.edist x y ≤ G.edist x v + G.edist v y := G.edist_triangle
        _ = (1 : ℕ∞) + 1 := by
          rw [SimpleGraph.edist_eq_one_iff_adj.mpr hvx.symm,
              SimpleGraph.edist_eq_one_iff_adj.mpr hyw.symm]
        _ = 2 := rfl
    exact absurd (h4.trans hle) (by decide)
  have hvw : ¬ G.Adj v w := by
    intro h
    have hle : G.edist x y ≤ 3 := by
      calc
        G.edist x y ≤ G.edist x v + G.edist v y := G.edist_triangle
        _ ≤ G.edist x v + (G.edist v w + G.edist w y) := add_le_add le_rfl G.edist_triangle
        _ = (1 : ℕ∞) + ((1 : ℕ∞) + 1) := by
          rw [SimpleGraph.edist_eq_one_iff_adj.mpr hvx.symm,
              SimpleGraph.edist_eq_one_iff_adj.mpr h,
              SimpleGraph.edist_eq_one_iff_adj.mpr hyw.symm]
        _ = 3 := rfl
    exact absurd (h4.trans hle) (by decide)
  exact ⟨hvw, hxy, hne_vw, hne_xy⟩

private lemma replaceYWithX_mem_imp {V : Type*} [DecidableEq V] {x y z : V} {I : Finset V}
    (hz : z ∈ replaceYWithX x y I) (hzx : z ≠ x) : z ∈ I := by
  unfold replaceYWithX at hz
  split_ifs at hz with hy
  · simp only [mem_insert, mem_erase] at hz
    rcases hz with rfl | ⟨_, hzI⟩
    · exact absurd rfl hzx
    · exact hzI
  · exact hz

/-- Main inductive engine for Theorem 1, parameterized by graph order `n = Fintype.card V`. -/
private theorem simultaneous_additional_edges_aux (hDel : MaxDegDeletionResiduePremise) :
    ∀ (n : ℕ) (V : Type u) [Fintype V] [DecidableEq V],
      Fintype.card V = n →
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset (V × V)),
        TerminalPairs G T →
        ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧
          (∀ p ∈ T, ¬ (p.1 ∈ I ∧ p.2 ∈ I)) ∧
          SimpleGraph.residue G ≤ I.card := by
  intro n
  induction n with
  | zero =>
    intro V _ _ hcard G _ T hT
    refine ⟨∅, by simp [SimpleGraph.IsIndepSet], ?_, ?_⟩
    · intro p _ ⟨h1, _⟩; exact absurd h1 (notMem_empty _)
    · have h0 : ∀ u : V, G.degree u = 0 := fun u =>
        (Fintype.card_eq_zero_iff.mp hcard).elim u
      rw [residue_eq_card_of_all_deg_zero G h0, hcard]
      exact le_rfl
  | succ m ih =>
    intro V _ _ hcard G _ T hT
    -- Case 1: all vertices have degree 0 (hence `T` is empty and `I = univ` achieves `residue G`).
    by_cases hall0 : ∀ u : V, G.degree u = 0
    · refine ⟨Finset.univ, ?_, ?_, ?_⟩
      · intro a _ b _ _ hadj
        have hpos : 0 < G.degree a := Finset.card_pos.mpr ⟨b, (G.mem_neighborFinset a b).mpr hadj⟩
        have ha0 := hall0 a
        omega
      · intro p hp _
        have hpos := (hT.pos_deg p hp).1
        have hp0 := hall0 p.1
        omega
      · rw [residue_eq_card_of_all_deg_zero G hall0, Finset.card_univ]
    -- Case 2: there exists a vertex of positive degree; choose a maximum-degree vertex `v`.
    · push Not at hall0
      obtain ⟨u₀, hu₀⟩ := hall0
      have hne : (Finset.univ : Finset V).Nonempty := ⟨u₀, mem_univ u₀⟩
      obtain ⟨v, _, hv_max⟩ := Finset.exists_max_image Finset.univ (fun u => G.degree u) hne
      have hv_max' : ∀ u : V, G.degree u ≤ G.degree v := fun u => hv_max u (mem_univ u)
      have hv_pos : 0 < G.degree v := by
        have := hv_max' u₀
        omega
      let V' := { u : V // u ≠ v }
      have hcard_V' : Fintype.card V' = m := by
        have h := card_subtype_ne v
        dsimp only [V']
        omega
      let G' : SimpleGraph V' := G.induce { u : V | u ≠ v }
      let T₁ : Finset (V × V) := T.filter (fun p => p.1 ≠ v ∧ p.2 ≠ v)
      have hT₁_sub : ∀ p ∈ T₁, p ∈ T ∧ p.1 ≠ v ∧ p.2 ≠ v := fun p hp => by
        simpa [T₁] using hp
      -- Split on whether any surviving terminal becomes isolated in `G - v`.
      by_cases hiso : ∃ p, ∃ hp : p ∈ T₁,
          G'.degree ⟨p.1, (hT₁_sub p hp).2.1⟩ = 0 ∨ G'.degree ⟨p.2, (hT₁_sub p hp).2.2⟩ = 0
      · -- Subcase 2b: some surviving terminal `x` in pair `p₀ ∈ T₁` has sole neighbor `v` in `G`.
        rcases hiso with ⟨p₀, hp₀_T₁, hdeg0⟩
        obtain ⟨hp₀_T, hp₀1_ne_v, hp₀2_ne_v⟩ := hT₁_sub p₀ hp₀_T₁
        -- Extract `(x, y)` symmetrically so that `x` is the isolated terminal and `y` its partner.
        have hxy_spec : ∃ x y : V, (p₀ = (x, y) ∨ p₀ = (y, x)) ∧
            x ≠ v ∧ y ≠ v ∧
            (∀ u : V, G.Adj x u ↔ u = v) ∧
            0 < G.degree y ∧ (4 : ℕ∞) ≤ G.edist x y := by
          rcases hdeg0 with h1 | h2
          · refine ⟨p₀.1, p₀.2, Or.inl rfl, hp₀1_ne_v, hp₀2_ne_v, ?_,
              (hT.pos_deg p₀ hp₀_T).2, hT.within_pair p₀ hp₀_T⟩
            exact sole_neighbor_of_induce_deg_zero G hp₀1_ne_v (hT.pos_deg p₀ hp₀_T).1 h1
          · refine ⟨p₀.2, p₀.1, Or.inr rfl, hp₀2_ne_v, hp₀1_ne_v, ?_,
              (hT.pos_deg p₀ hp₀_T).1, SimpleGraph.edist_comm ▸ hT.within_pair p₀ hp₀_T⟩
            exact sole_neighbor_of_induce_deg_zero G hp₀2_ne_v (hT.pos_deg p₀ hp₀_T).2 h2
        rcases hxy_spec with ⟨x, y, hp₀_eq, hxv, hyv, hsole, hy_pos, hed_xy⟩
        have hvx : G.Adj v x := ((hsole v).mpr rfl).symm
        obtain ⟨w, hw_mem⟩ := Finset.card_pos.mp hy_pos
        have hyw : G.Adj y w := (G.mem_neighborFinset y w).mp hw_mem
        obtain ⟨hvw, hxy, hne_vw, hne_xy⟩ := edist_ge_four_implies_switch_conds G hvx hyw hed_xy
        let H : SimpleGraph V := twoSwitch G v x y w
        let H' : SimpleGraph V' := H.induce { u : V | u ≠ v }
        let T₂ : Finset (V × V) := T₁.erase p₀
        -- Every terminal of `T₂` is distinct from `v, x, y, w` and had positive degree in `G'`.
        have hterm_props : ∀ q ∈ T₂, ∀ z : V, (z = q.1 ∨ z = q.2) →
            z ≠ v ∧ z ≠ x ∧ z ≠ y ∧ z ≠ w := by
          intro q hq z hz
          have hq_ne : q ≠ p₀ := (mem_erase.mp hq).1
          have hq_T₁ : q ∈ T₁ := (mem_erase.mp hq).2
          obtain ⟨hq_T, hq1v, hq2v⟩ := hT₁_sub q hq_T₁
          have hzv : z ≠ v := by rcases hz with rfl | rfl <;> assumption
          have hx_in_p0 : x = p₀.1 ∨ x = p₀.2 := by
            rcases hp₀_eq with h | h <;> simp [h]
          have hy_in_p0 : y = p₀.1 ∨ y = p₀.2 := by
            rcases hp₀_eq with h | h <;> simp [h]
          have hzx : z ≠ x := by
            intro h
            have h3 := hT.between_pairs q hq_T p₀ hp₀_T hq_ne
            have h3' : (3 : ℕ∞) ≤ G.edist z x := by
              rcases hz with rfl | rfl <;> rcases hx_in_p0 with rfl | rfl
              · exact h3.1
              · exact h3.2.1
              · exact h3.2.2.1
              · exact h3.2.2.2
            rw [h, SimpleGraph.edist_self] at h3'
            exact absurd h3' (by decide)
          have hzy : z ≠ y := by
            intro h
            have h3 := hT.between_pairs q hq_T p₀ hp₀_T hq_ne
            have h3' : (3 : ℕ∞) ≤ G.edist z y := by
              rcases hz with rfl | rfl <;> rcases hy_in_p0 with rfl | rfl
              · exact h3.1
              · exact h3.2.1
              · exact h3.2.2.1
              · exact h3.2.2.2
            rw [h, SimpleGraph.edist_self] at h3'
            exact absurd h3' (by decide)
          have hzw : z ≠ w := by
            intro h
            have hed_yz : (3 : ℕ∞) ≤ G.edist y z :=
              hT.edist_ge_three_of_terminals hp₀_T hq_T hy_in_p0 hz (by rw [h]; exact hyw.ne)
            rw [h, SimpleGraph.edist_eq_one_iff_adj.mpr hyw] at hed_yz
            exact absurd hed_yz (by decide)
          exact ⟨hzv, hzx, hzy, hzw⟩
        have hterm_pos_H' : ∀ q, ∀ hq : q ∈ T₂, ∀ z : V, (hz : z = q.1 ∨ z = q.2) →
            0 < H'.degree ⟨z, (hterm_props q hq z hz).1⟩ := by
          intro q hq z hz
          obtain ⟨hzv, hzx, hzy, hzw⟩ := hterm_props q hq z hz
          have hq_T : q ∈ T := (hT₁_sub q (mem_erase.mp hq).2).1
          have hz_pos_G : 0 < G.degree z := by
            rcases hz with rfl | rfl
            · exact (hT.pos_deg q hq_T).1
            · exact (hT.pos_deg q hq_T).2
          -- `z` cannot have sole neighbor `v` (otherwise `edist x z ≤ 2`, contradicting `≥ 3`).
          have hz_pos_G' : 0 < G'.degree ⟨z, hzv⟩ := by
            by_contra hle
            have hdeg0' : G'.degree ⟨z, hzv⟩ = 0 := by omega
            have hsole_z := sole_neighbor_of_induce_deg_zero G hzv hz_pos_G hdeg0'
            have hzv_adj : G.Adj z v := (hsole_z v).mpr rfl
            have hx_in_p0 : x = p₀.1 ∨ x = p₀.2 := by
              rcases hp₀_eq with h | h <;> simp [h]
            have h3 : (3 : ℕ∞) ≤ G.edist x z :=
              hT.edist_ge_three_of_terminals hp₀_T hq_T hx_in_p0 hz hzx.symm
            have hle2 : G.edist x z ≤ 2 := by
              calc
                G.edist x z ≤ G.edist x v + G.edist v z := G.edist_triangle
                _ = (1 : ℕ∞) + 1 := by
                  rw [SimpleGraph.edist_eq_one_iff_adj.mpr hvx.symm,
                      SimpleGraph.edist_eq_one_iff_adj.mpr hzv_adj.symm]
                _ = 2 := rfl
            exact absurd (h3.trans hle2) (by decide)
          obtain ⟨u', hu'⟩ := Finset.card_pos.mp hz_pos_G'
          have hGzu : G.Adj z u'.1 := (G'.mem_neighborFinset ⟨z, hzv⟩ u').mp hu'
          have hHzu : H.Adj z u'.1 := by
            have hnb := twoSwitch_neighborFinset_other G hne_vw hne_xy hzv hzx hzy hzw
            have : u'.1 ∈ H.neighborFinset z := by
              rw [hnb]; exact (G.mem_neighborFinset z u'.1).mpr hGzu
            exact (H.mem_neighborFinset z u'.1).mp this
          exact Finset.card_pos.mpr ⟨u', (H'.mem_neighborFinset ⟨z, hzv⟩ u').mpr hHzu⟩
        -- Lift `T₂` into `V' × V'`.
        let liftPair : { q : V × V // q ∈ T₂ } → V' × V' := fun q =>
          (⟨q.1.1, (hterm_props q.1 q.2 q.1.1 (Or.inl rfl)).1⟩,
           ⟨q.1.2, (hterm_props q.1 q.2 q.1.2 (Or.inr rfl)).1⟩)
        let T₂' : Finset (V' × V') := T₂.attach.image liftPair
        have hT₂'_valid : TerminalPairs H' T₂' := by
          refine ⟨?_, ?_, ?_⟩
          · intro q' hq'
            rcases mem_image.mp hq' with ⟨⟨q, hq⟩, _, rfl⟩
            exact ⟨hterm_pos_H' q hq q.1 (Or.inl rfl), hterm_pos_H' q hq q.2 (Or.inr rfl)⟩
          · intro q' hq'
            rcases mem_image.mp hq' with ⟨⟨q, hq⟩, _, rfl⟩
            have hq_T : q ∈ T := (hT₁_sub q (mem_erase.mp hq).2).1
            have h1x : q.1 ≠ x := (hterm_props q hq q.1 (Or.inl rfl)).2.1
            have h2x : q.2 ≠ x := (hterm_props q hq q.2 (Or.inr rfl)).2.1
            exact (hT.within_pair q hq_T).trans
              (edist_le_twoSwitch_induce_edist G hsole hyw hvw hne_vw hne_xy
                (liftPair ⟨q, hq⟩).1 (liftPair ⟨q, hq⟩).2 h1x h2x)
          · intro q₁' hq₁' q₂' hq₂' hne'
            rcases mem_image.mp hq₁' with ⟨⟨q₁, hq₁⟩, _, rfl⟩
            rcases mem_image.mp hq₂' with ⟨⟨q₂, hq₂⟩, _, rfl⟩
            have hqne : q₁ ≠ q₂ := by
              intro heq
              apply hne'
              cases q₁; cases q₂
              simp only [Prod.mk.injEq] at heq
              rcases heq with ⟨rfl, rfl⟩
              rfl
            have hq₁_T : q₁ ∈ T := (hT₁_sub q₁ (mem_erase.mp hq₁).2).1
            have hq₂_T : q₂ ∈ T := (hT₁_sub q₂ (mem_erase.mp hq₂).2).1
            obtain ⟨h11, h12, h21, h22⟩ := hT.between_pairs q₁ hq₁_T q₂ hq₂_T hqne
            have hq11x := (hterm_props q₁ hq₁ q₁.1 (Or.inl rfl)).2.1
            have hq12x := (hterm_props q₁ hq₁ q₁.2 (Or.inr rfl)).2.1
            have hq21x := (hterm_props q₂ hq₂ q₂.1 (Or.inl rfl)).2.1
            have hq22x := (hterm_props q₂ hq₂ q₂.2 (Or.inr rfl)).2.1
            exact ⟨h11.trans (edist_le_twoSwitch_induce_edist G hsole hyw hvw hne_vw hne_xy
                     (liftPair ⟨q₁, hq₁⟩).1 (liftPair ⟨q₂, hq₂⟩).1 hq11x hq21x),
                   h12.trans (edist_le_twoSwitch_induce_edist G hsole hyw hvw hne_vw hne_xy
                     (liftPair ⟨q₁, hq₁⟩).1 (liftPair ⟨q₂, hq₂⟩).2 hq11x hq22x),
                   h21.trans (edist_le_twoSwitch_induce_edist G hsole hyw hvw hne_vw hne_xy
                     (liftPair ⟨q₁, hq₁⟩).2 (liftPair ⟨q₂, hq₂⟩).1 hq12x hq21x),
                   h22.trans (edist_le_twoSwitch_induce_edist G hsole hyw hvw hne_vw hne_xy
                     (liftPair ⟨q₁, hq₁⟩).2 (liftPair ⟨q₂, hq₂⟩).2 hq12x hq22x)⟩
        -- Apply induction hypothesis to `(H', T₂')`.
        obtain ⟨I', hI'_indep, hI'_pairs, hI'_card⟩ := ih V' hcard_V' H' T₂' hT₂'_valid
        let I_H : Finset V := I'.map ⟨Subtype.val, Subtype.val_injective⟩
        have hIH_indep : H.IsIndepSet (I_H : Set V) := by
          intro a ha b hb hab
          rw [mem_coe, mem_map] at ha hb
          rcases ha with ⟨a0, ha0, rfl⟩
          rcases hb with ⟨b0, hb0, rfl⟩
          exact hI'_indep (mem_coe.mpr ha0) (mem_coe.mpr hb0) (fun h => hab (congrArg Subtype.val h))
        have hv_not_IH : v ∉ I_H := by
          simp only [I_H, mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
          rintro ⟨u, hu⟩ _ huv
          exact hu huv
        have hIH_card : I_H.card = I'.card := card_map _
        -- Transfer via `firstIsolation_switch`: `I_G = replaceYWithX x y I_H`.
        obtain ⟨hH_deg, hH_res, hH_max, hSwitch⟩ :=
          firstIsolation_switch G hsole hyw hvw hxy hne_vw hne_xy
        obtain ⟨hIG_indep, hv_not_IG, hy_not_IG, hIG_card⟩ := hSwitch I_H hIH_indep hv_not_IH
        let I_G : Finset V := replaceYWithX x y I_H
        refine ⟨I_G, hIG_indep, ?_, ?_⟩
        · intro q hq ⟨hq1, hq2⟩
          by_cases hqv : q.1 = v ∨ q.2 = v
          · rcases hqv with h1 | h2
            · exact hv_not_IG (h1 ▸ hq1)
            · exact hv_not_IG (h2 ▸ hq2)
          · push Not at hqv
            have hq_T₁ : q ∈ T₁ := mem_filter.mpr ⟨hq, hqv⟩
            by_cases hqp0 : q = p₀
            · subst hqp0
              rcases hp₀_eq with heq | heq
              · rw [heq] at hq2; exact hy_not_IG hq2
              · rw [heq] at hq1; exact hy_not_IG hq1
            · have hq_T₂ : q ∈ T₂ := mem_erase.mpr ⟨hqp0, hq_T₁⟩
              have hq1x : q.1 ≠ x := (hterm_props q hq_T₂ q.1 (Or.inl rfl)).2.1
              have hq2x : q.2 ≠ x := (hterm_props q hq_T₂ q.2 (Or.inr rfl)).2.1
              have hq1_IH : q.1 ∈ I_H := replaceYWithX_mem_imp hq1 hq1x
              have hq2_IH : q.2 ∈ I_H := replaceYWithX_mem_imp hq2 hq2x
              have hq1_I' : (⟨q.1, hqv.1⟩ : V') ∈ I' := by
                rcases mem_map.mp hq1_IH with ⟨u, hu, hu_eq⟩
                have : u = ⟨q.1, hqv.1⟩ := Subtype.ext hu_eq
                exact this ▸ hu
              have hq2_I' : (⟨q.2, hqv.2⟩ : V') ∈ I' := by
                rcases mem_map.mp hq2_IH with ⟨u, hu, hu_eq⟩
                have : u = ⟨q.2, hqv.2⟩ := Subtype.ext hu_eq
                exact this ▸ hu
              have hmem_T₂' : liftPair ⟨q, hq_T₂⟩ ∈ T₂' :=
                mem_image.mpr ⟨⟨q, hq_T₂⟩, mem_attach _ _, rfl⟩
              exact hI'_pairs (liftPair ⟨q, hq_T₂⟩) hmem_T₂' ⟨hq1_I', hq2_I'⟩
        · have hH_vpos : 0 < H.degree v := by rw [hH_deg v]; exact hv_pos
          have hdel_H : SimpleGraph.residue H ≤ SimpleGraph.residue H' :=
            hDel.apply H v (hH_max hv_max') hH_vpos
          calc
            SimpleGraph.residue G = SimpleGraph.residue H := hH_res.symm
            _ ≤ SimpleGraph.residue H' := hdel_H
            _ ≤ I'.card := hI'_card
            _ = I_H.card := hIH_card.symm
            _ = I_G.card := hIG_card.symm
      · -- Subcase 2a: no surviving terminal becomes isolated in `G' = G - v`.
        push Not at hiso
        let liftPair : { q : V × V // q ∈ T₁ } → V' × V' := fun q =>
          (⟨q.1.1, (hT₁_sub q.1 q.2).2.1⟩, ⟨q.1.2, (hT₁_sub q.1 q.2).2.2⟩)
        let T₁' : Finset (V' × V') := T₁.attach.image liftPair
        have hT₁'_valid : TerminalPairs G' T₁' := by
          refine ⟨?_, ?_, ?_⟩
          · intro q' hq'
            rcases mem_image.mp hq' with ⟨⟨q, hq⟩, _, rfl⟩
            obtain ⟨h1, h2⟩ := hiso q hq
            exact ⟨Nat.pos_of_ne_zero h1, Nat.pos_of_ne_zero h2⟩
          · intro q' hq'
            rcases mem_image.mp hq' with ⟨⟨q, hq⟩, _, rfl⟩
            exact (hT.within_pair q (hT₁_sub q hq).1).trans
              (edist_le_induce_edist G _ (liftPair ⟨q, hq⟩).1 (liftPair ⟨q, hq⟩).2)
          · intro q₁' hq₁' q₂' hq₂' hne'
            rcases mem_image.mp hq₁' with ⟨⟨q₁, hq₁⟩, _, rfl⟩
            rcases mem_image.mp hq₂' with ⟨⟨q₂, hq₂⟩, _, rfl⟩
            have hqne : q₁ ≠ q₂ := by
              intro heq
              apply hne'
              cases q₁; cases q₂
              simp only [Prod.mk.injEq] at heq
              rcases heq with ⟨rfl, rfl⟩
              rfl
            obtain ⟨h11, h12, h21, h22⟩ :=
              hT.between_pairs q₁ (hT₁_sub q₁ hq₁).1 q₂ (hT₁_sub q₂ hq₂).1 hqne
            exact ⟨h11.trans (edist_le_induce_edist G _ (liftPair ⟨q₁, hq₁⟩).1 (liftPair ⟨q₂, hq₂⟩).1),
                   h12.trans (edist_le_induce_edist G _ (liftPair ⟨q₁, hq₁⟩).1 (liftPair ⟨q₂, hq₂⟩).2),
                   h21.trans (edist_le_induce_edist G _ (liftPair ⟨q₁, hq₁⟩).2 (liftPair ⟨q₂, hq₂⟩).1),
                   h22.trans (edist_le_induce_edist G _ (liftPair ⟨q₁, hq₁⟩).2 (liftPair ⟨q₂, hq₂⟩).2)⟩
        obtain ⟨I', hI'_indep, hI'_pairs, hI'_card⟩ := ih V' hcard_V' G' T₁' hT₁'_valid
        let I : Finset V := I'.map ⟨Subtype.val, Subtype.val_injective⟩
        have hI_indep : G.IsIndepSet (I : Set V) := by
          intro a ha b hb hab
          rw [mem_coe, mem_map] at ha hb
          rcases ha with ⟨a0, ha0, rfl⟩
          rcases hb with ⟨b0, hb0, rfl⟩
          exact hI'_indep (mem_coe.mpr ha0) (mem_coe.mpr hb0) (fun h => hab (congrArg Subtype.val h))
        have hv_not_I : v ∉ I := by
          simp only [I, mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
          rintro ⟨u, hu⟩ _ huv
          exact hu huv
        refine ⟨I, hI_indep, ?_, ?_⟩
        · intro q hq ⟨hq1, hq2⟩
          by_cases hqv : q.1 = v ∨ q.2 = v
          · rcases hqv with h1 | h2
            · exact hv_not_I (h1 ▸ hq1)
            · exact hv_not_I (h2 ▸ hq2)
          · push Not at hqv
            have hq_T₁ : q ∈ T₁ := mem_filter.mpr ⟨hq, hqv⟩
            have hq1_I' : (⟨q.1, hqv.1⟩ : V') ∈ I' := by
              rcases mem_map.mp hq1 with ⟨u, hu, hu_eq⟩
              have : u = ⟨q.1, hqv.1⟩ := Subtype.ext hu_eq
              exact this ▸ hu
            have hq2_I' : (⟨q.2, hqv.2⟩ : V') ∈ I' := by
              rcases mem_map.mp hq2 with ⟨u, hu, hu_eq⟩
              have : u = ⟨q.2, hqv.2⟩ := Subtype.ext hu_eq
              exact this ▸ hu
            have hmem_T₁' : liftPair ⟨q, hq_T₁⟩ ∈ T₁' :=
              mem_image.mpr ⟨⟨q, hq_T₁⟩, mem_attach _ _, rfl⟩
            exact hI'_pairs (liftPair ⟨q, hq_T₁⟩) hmem_T₁' ⟨hq1_I', hq2_I'⟩
        · have hdel_G : SimpleGraph.residue G ≤ SimpleGraph.residue G' :=
            hDel.apply G v hv_max' hv_pos
          calc
            SimpleGraph.residue G ≤ SimpleGraph.residue G' := hdel_G
            _ ≤ I'.card := hI'_card
            _ = I.card := (card_map _).symm

/--
**Theorem 1 (Simultaneous Additional Edges, conditional on `MaxDegDeletionResiduePremise`):**
For every finite simple graph `G` and every family `T` of disjoint terminal pairs with
positive degrees, within-pair `edist ≥ 4`, and between-pair `edist ≥ 3`, there exists an
independent set `I` of `G` avoiding both endpoints of every pair in `T` with
`SimpleGraph.residue G ≤ I.card`.
-/
theorem simultaneous_additional_edges_of_maxDegDeletion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hDel : MaxDegDeletionResiduePremise) :
    SatisfiesTerminalPairProperty G := fun T hT =>
  simultaneous_additional_edges_aux hDel (Fintype.card V) V rfl G T hT

/-- **Theorem 1 (Graph-Addition Form, `R(G) ≤ α(G + T)`):**
under `MaxDegDeletionResiduePremise`, adding the pair edges `T` preserves an independent set
of size at least `SimpleGraph.residue G`. -/
theorem residue_le_indepNum_addPairs_of_maxDegDeletion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (V × V)) (hT : TerminalPairs G T)
    (hDel : MaxDegDeletionResiduePremise) :
    SimpleGraph.residue G ≤ (addPairs G T).indepNum := by
  obtain ⟨I, hI_indep, hI_avoid, hI_card⟩ :=
    simultaneous_additional_edges_of_maxDegDeletion G hDel T hT
  have hI_add : (addPairs G T).IsIndepSet (I : Set V) :=
    (addPairs_isIndepSet_iff (fun p hp => hT.ne_of_mem hp) I).mpr ⟨hI_indep, hI_avoid⟩
  exact hI_card.trans hI_add.card_le_indepNum

/-- **Favaron–Mahéo–Saclé Bound (`R(G) ≤ α(G)`), derived from `MaxDegDeletionResiduePremise`:**
applying Theorem 1 to the empty pair family `T = ∅`. -/
theorem residue_le_indepNum_of_maxDegDeletion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hDel : MaxDegDeletionResiduePremise) :
    SimpleGraph.residue G ≤ G.indepNum := by
  have hEmpty : TerminalPairs G ∅ := ⟨by simp, by simp, by simp⟩
  obtain ⟨I, hI_indep, _, hI_card⟩ :=
    simultaneous_additional_edges_of_maxDegDeletion G hDel ∅ hEmpty
  exact hI_card.trans hI_indep.card_le_indepNum

/-- **Single-Pair Corollary (`packing.md` remark):**
for any two positive-degree vertices `x, y` with `G.edist x y ≥ 4`, under
`MaxDegDeletionResiduePremise` there is an independent set of cardinality at least
`SimpleGraph.residue G` omitting at least one of `x, y`. -/
theorem exists_indepSet_avoiding_single_pair_of_maxDegDeletion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V}
    (hx : 0 < G.degree x) (hy : 0 < G.degree y) (h4 : (4 : ℕ∞) ≤ G.edist x y)
    (hDel : MaxDegDeletionResiduePremise) :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ ¬ (x ∈ I ∧ y ∈ I) ∧
      SimpleGraph.residue G ≤ I.card := by
  have hSingle : TerminalPairs G {(x, y)} := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp; rw [mem_singleton.mp hp]; exact ⟨hx, hy⟩
    · intro p hp; rw [mem_singleton.mp hp]; exact h4
    · intro p hp q hq hne
      rw [mem_singleton.mp hp, mem_singleton.mp hq] at hne
      exact absurd rfl hne
  obtain ⟨I, hI_indep, hI_avoid, hI_card⟩ :=
    simultaneous_additional_edges_of_maxDegDeletion G hDel {(x, y)} hSingle
  exact ⟨I, hI_indep, hI_avoid (x, y) (mem_singleton_self _), hI_card⟩

end SimultaneousAdditionalEdges

/-! ## 4. Theorem 2: Uniform `⌊(2D + 6) / 7⌋` Bound and 12-Diameter Corollaries -/

section UniformDiameterBound

/--
**Theorem 2 (Uniform Diameter Bound, conditional on `MaxDegDeletionResiduePremise`):**
For every nonempty finite connected simple graph `G` (including all connected graphs on at
least two vertices),
`SimpleGraph.residue G + (2 * G.diam + 6) / 7 ≤ G.largestInducedForestSize`.
-/
theorem uniform_diam_bound_of_maxDegDeletion
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hDel : MaxDegDeletionResiduePremise) :
    SimpleGraph.residue G + (2 * G.diam + 6) / 7 ≤ G.largestInducedForestSize :=
  uniform_diam_bound_of_pair_property G hconn
    (simultaneous_additional_edges_of_maxDegDeletion G hDel)

/--
**Corollary (WOWII Conjecture 61 for 12 Exact Diameters, `ℕ`-form):**
Under `MaxDegDeletionResiduePremise`, for every nontrivial finite connected graph `G` with
`G.diam ∈ {1, 2, 3, 4, 5, 6, 8, 9, 11, 12, 15, 18}`,
`SimpleGraph.residue G + (G.diam + 2) / 3 ≤ G.largestInducedForestSize`.
-/
theorem wowii61_of_twelve_diams_of_maxDegDeletion
    {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hD : G.diam = 1 ∨ G.diam = 2 ∨ G.diam = 3 ∨ G.diam = 4 ∨ G.diam = 5 ∨ G.diam = 6 ∨
          G.diam = 8 ∨ G.diam = 9 ∨ G.diam = 11 ∨ G.diam = 12 ∨ G.diam = 15 ∨ G.diam = 18)
    (hDel : MaxDegDeletionResiduePremise) :
    SimpleGraph.residue G + (G.diam + 2) / 3 ≤ G.largestInducedForestSize :=
  wowii61_of_twelve_diams_of_pair_property G hconn hD
    (simultaneous_additional_edges_of_maxDegDeletion G hDel)

end UniformDiameterBound

end WOWII61.PackingBound
