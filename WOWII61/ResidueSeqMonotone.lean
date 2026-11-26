module

public import WOWII61.ResidueSeqDefs

/-!
# Havel–Hakimi Sequence Monotonicity Theorem (`WOWII61.ResidueSeq`)

Implements the self-contained simultaneous induction (Theorem 1 of
Triesch dominance / exchange monotonicity on the exact `SimpleGraph.residueAux` and
`SimpleGraph.havelHakimiStep` from `StagedDeps.Residue`:

- **Option A (`residueAux_le_of_exchangeStep`):**
  For descending HH-valid lists `s₁, s₂` related by one elementary raising transfer
  `(a, b) ↦ (a + 1, b - 1)` (`a ≥ b ≥ 1`),
  `SimpleGraph.residueAux s₁ ≤ SimpleGraph.residueAux s₂`.
- **Theorem 1(B) (`residueAux_le_of_safeDoubleDec`):**
  For descending HH-valid lists `b, a` with `SafeDoubleDec b a`,
  `SimpleGraph.residueAux b ≤ SimpleGraph.residueAux a`.
- **Transitive HH-valid chain (`residueAux_le_of_hhValid_exchangeChain`):**
  Directly consumes `Relation.ReflTransGen (fun a b => ExchangeStep a b ∧ IsHHValid a ∧ IsHHValid b)`.
- **Leaf-edge decrement & trailing zero (`residueAux_le_of_leaf_edge_dec`, `residueAux_append_zero`).**

Purely arithmetic over `List ℕ` and `Multiset ℕ`; zero `SimpleGraph` construction machinery.
-/

@[expose] public section

namespace WOWII61.ResidueSeq

open SimpleGraph

/-! ## 1. Auxiliary Multiset & Split Helpers -/

private theorem exists_cons_cons_of_getElem_ne (l : List ℕ) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hne : i ≠ j) :
    ∃ M : Multiset ℕ, (l : Multiset ℕ) = l[i] ::ₘ l[j] ::ₘ M := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons a t ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hne
      | succ j' =>
        have hj' : j' < t.length := by simp at hj; omega
        have hmem : t[j'] ∈ (t : Multiset ℕ) := Multiset.mem_coe.mpr (List.getElem_mem hj')
        obtain ⟨M, hM⟩ := Multiset.exists_cons_of_mem hmem
        refine ⟨M, ?_⟩
        change a ::ₘ (t : Multiset ℕ) = a ::ₘ t[j'] ::ₘ M
        rw [hM]
    | succ i' =>
      cases j with
      | zero =>
        have hi' : i' < t.length := by simp at hi; omega
        have hmem : t[i'] ∈ (t : Multiset ℕ) := Multiset.mem_coe.mpr (List.getElem_mem hi')
        obtain ⟨M, hM⟩ := Multiset.exists_cons_of_mem hmem
        refine ⟨M, ?_⟩
        change a ::ₘ (t : Multiset ℕ) = t[i'] ::ₘ a ::ₘ M
        rw [hM, Multiset.cons_swap]
      | succ j' =>
        have hi' : i' < t.length := by simp at hi; omega
        have hj' : j' < t.length := by simp at hj; omega
        obtain ⟨M, hM⟩ := ih hi' hj' (by omega)
        refine ⟨a ::ₘ M, ?_⟩
        change a ::ₘ (t : Multiset ℕ) = t[i'] ::ₘ t[j'] ::ₘ a ::ₘ M
        rw [hM, Multiset.cons_swap a t[i'], Multiset.cons_swap a t[j']]

private theorem coe_set_two (l : List ℕ) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hne : i ≠ j) (u' v' : ℕ) :
    ∃ M : Multiset ℕ,
      (l : Multiset ℕ) = l[i] ::ₘ l[j] ::ₘ M ∧
      (((l.set i u').set j v' : List ℕ) : Multiset ℕ) = u' ::ₘ v' ::ₘ M := by
  obtain ⟨M, hM⟩ := exists_cons_cons_of_getElem_ne l hi hj hne
  have hmid : ((l.set i u' : List ℕ) : Multiset ℕ) = l[j] ::ₘ (u' ::ₘ M) := by
    rw [coe_set_eq_of_coe_cons hi rfl hM, Multiset.cons_swap]
  have hj' : j < (l.set i u').length := by rw [List.length_set]; exact hj
  have hval_j : (l.set i u')[j]'hj' = l[j] := by
    rw [List.getElem_set]
    simp [hne]
  have hfin : (((l.set i u').set j v' : List ℕ) : Multiset ℕ) = u' ::ₘ v' ::ₘ M := by
    rw [coe_set_eq_of_coe_cons hj' hval_j hmid, Multiset.cons_swap]
  exact ⟨M, hM, hfin⟩

private theorem coe_phiStep_split_succ {d : ℕ} {l : List ℕ} (hd : d < l.length) :
    (phiStep d l : Multiset ℕ) =
      (((l.take d).map (· - 1) : List ℕ) : Multiset ℕ) +
        (l[d] ::ₘ (l.drop (d + 1) : Multiset ℕ)) ∧
    (phiStep (d + 1) l : Multiset ℕ) =
      (((l.take d).map (· - 1) : List ℕ) : Multiset ℕ) +
        ((l[d] - 1) ::ₘ (l.drop (d + 1) : Multiset ℕ)) := by
  have hdrop : l.drop d = l[d] :: l.drop (d + 1) := by
    simp [List.cons_getElem_drop_succ (h := hd)]
  have htake : l.take (d + 1) = l.take d ++ [l[d]] :=
    List.take_succ_eq_append_getElem hd
  constructor
  · rw [coe_phiStep, hdrop, ← Multiset.coe_add]
    rfl
  · rw [coe_phiStep, htake, List.map_append, List.map_singleton, ← Multiset.coe_add,
        ← Multiset.coe_add]
    change (((l.take d).map (· - 1) : List ℕ) : Multiset ℕ) +
        ((l[d] - 1) ::ₘ (0 : Multiset ℕ)) + (l.drop (d + 1) : Multiset ℕ) = _
    rw [add_assoc, Multiset.cons_add, zero_add]

private theorem mem_phiStep_of_mem_take {d : ℕ} {l : List ℕ} {x : ℕ} (hx : x ∈ l.take d) :
    x - 1 ∈ phiStep d l := by
  rw [← Multiset.mem_coe, coe_phiStep, ← Multiset.coe_add, Multiset.mem_add]
  exact Or.inl (Multiset.mem_coe.mpr (List.mem_map_of_mem hx))

private theorem mem_phiStep_of_mem_drop {d : ℕ} {l : List ℕ} {x : ℕ} (hx : x ∈ l.drop d) :
    x ∈ phiStep d l := by
  rw [← Multiset.mem_coe, coe_phiStep, ← Multiset.coe_add, Multiset.mem_add]
  exact Or.inr (Multiset.mem_coe.mpr hx)

/-! ## 2. Case A1: Raising Transfer Not Involving the Head `d` -/

private theorem exchangeStep_caseA1 {d : ℕ} {rb ra : List ℕ}
    (hEx : ExchangeStep rb ra)
    (hd : d ≤ rb.length)
    (hpos_ra : ∀ z ∈ ra.take d, 1 ≤ z) :
    phiStep d rb = phiStep d ra ∨ ExchangeStep (phiStep d rb) (phiStep d ra) := by
  rcases hEx with ⟨hrb_pw, hra_pw, m, u, v, hvu, hv1, hrb_coe, hra_coe⟩
  have hu_mem : u ∈ rb := by
    rw [← Multiset.mem_coe, hrb_coe]
    exact Multiset.mem_cons_self u _
  obtain ⟨i, hi, hrb_i, hfirst⟩ := exists_first_idx hrb_pw hu_mem
  let mid := rb.set i (u + 1)
  have hmid_pw : mid.Pairwise (· ≥ ·) := pairwise_set_inc_first hrb_pw hi hrb_i hfirst
  have hmid_coe : (mid : Multiset ℕ) = (u + 1) ::ₘ v ::ₘ m :=
    coe_set_eq_of_coe_cons hi hrb_i hrb_coe
  have hmid_len : mid.length = rb.length := List.length_set
  have hv_mem : v ∈ mid := by
    rw [← Multiset.mem_coe, hmid_coe]
    exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self v m)
  obtain ⟨j, hj_mid, hmid_j, hlast⟩ := exists_last_idx hmid_pw hv_mem
  have hj : j < rb.length := by omega
  have hij : i < j := by
    by_contra hji
    have hle : j ≤ i := Nat.le_of_not_lt hji
    have hi_mid : i < mid.length := by omega
    have hge : mid[i]'hi_mid ≤ mid[j]'hj_mid := getElem_ge_of_pairwise_ge hmid_pw hj_mid hi_mid hle
    have hmid_i : mid[i]'hi_mid = u + 1 := by simp [mid]
    rw [hmid_i, hmid_j] at hge
    omega
  have hrb_j : rb[j]'hj = v := by
    have hne : i ≠ j := by omega
    have : mid[j]'hj_mid = rb[j]'hj := by simp [mid, hne]
    omega
  have hra_eq : ra = mid.set j (v - 1) := by
    have hpw := pairwise_set_dec_last hmid_pw hj_mid hmid_j hlast
    have hcoe : ((mid.set j (v - 1) : List ℕ) : Multiset ℕ) = (u + 1) ::ₘ (v - 1) ::ₘ m := by
      have hmid_swap : (mid : Multiset ℕ) = v ::ₘ ((u + 1) ::ₘ m) := by
        rw [hmid_coe, Multiset.cons_swap]
      rw [coe_set_eq_of_coe_cons hj_mid hmid_j hmid_swap, Multiset.cons_swap]
    exact eq_of_coe_eq_of_pairwise hra_pw hpw (by rw [hra_coe, hcoe])
  -- Split on positions of i < j relative to d
  by_cases hjd : j < d
  · -- Both i and j are < d
    have hid : i < d := by omega
    have hra_take : ra.take d = ((rb.take d).set i (u + 1)).set j (v - 1) := by
      rw [hra_eq, take_set_of_lt _ hjd, take_set_of_lt _ hid]
    have hra_drop : ra.drop d = rb.drop d := by
      rw [hra_eq, drop_set_of_lt _ hjd, drop_set_of_lt _ hid]
    have hi_t : i < (rb.take d).length := by rw [List.length_take_of_le hd]; exact hid
    have hj_t : j < (rb.take d).length := by rw [List.length_take_of_le hd]; exact hjd
    have hv2 : 1 ≤ v - 1 := by
      have hj_ra : j < (ra.take d).length := by
        rw [hra_take, List.length_set, List.length_set]; exact hj_t
      have hmem : (ra.take d)[j]'hj_ra ∈ ra.take d := List.getElem_mem hj_ra
      have hval : (ra.take d)[j]'hj_ra = v - 1 := by simp [hra_take]
      rw [hval] at hmem
      exact hpos_ra (v - 1) hmem
    have hmap_eq : (ra.take d).map (· - 1) =
        (((rb.take d).map (· - 1)).set i u).set j (v - 1 - 1) := by
      rw [hra_take, List.map_set, List.map_set]
      have : (u + 1) - 1 = u := by omega
      rw [this]
    have hi_m : i < ((rb.take d).map (· - 1)).length := by rw [List.length_map]; exact hi_t
    have hj_m : j < ((rb.take d).map (· - 1)).length := by rw [List.length_map]; exact hj_t
    obtain ⟨M₀, hM₀_b, hM₀_a⟩ := coe_set_two ((rb.take d).map (· - 1)) hi_m hj_m (by omega) u (v - 1 - 1)
    have hmi : ((rb.take d).map (· - 1))[i]'hi_m = u - 1 := by simp [List.getElem_take, hrb_i]
    have hmj : ((rb.take d).map (· - 1))[j]'hj_m = v - 1 := by simp [List.getElem_take, hrb_j]
    rw [hmi, hmj] at hM₀_b
    rw [← hmap_eq] at hM₀_a
    refine Or.inr ⟨pairwise_phiStep d rb, pairwise_phiStep d ra,
      M₀ + (rb.drop d : Multiset ℕ), u - 1, v - 1, by omega, hv2, ?_, ?_⟩
    · rw [coe_phiStep, ← Multiset.coe_add, hM₀_b, Multiset.cons_add, Multiset.cons_add]
    · rw [coe_phiStep, ← Multiset.coe_add, hM₀_a, hra_drop, Multiset.cons_add, Multiset.cons_add]
      have : (u - 1) + 1 = u := by omega
      rw [this]
  · by_cases hdi : d ≤ i
    · -- Both i and j are ≥ d
      have hdj : d ≤ j := by omega
      have hra_take : ra.take d = rb.take d := by
        rw [hra_eq, take_set_of_ge _ hdj, take_set_of_ge _ hdi]
      have hra_drop : ra.drop d = ((rb.drop d).set (i - d) (u + 1)).set (j - d) (v - 1) := by
        rw [hra_eq, drop_set_of_ge _ hdj, drop_set_of_ge _ hdi]
      have hi_d : i - d < (rb.drop d).length := by rw [List.length_drop]; omega
      have hj_d : j - d < (rb.drop d).length := by rw [List.length_drop]; omega
      obtain ⟨M₀, hM₀_b, hM₀_a⟩ :=
        coe_set_two (rb.drop d) hi_d hj_d (by omega) (u + 1) (v - 1)
      have hdi_val : (rb.drop d)[i - d]'hi_d = u := by
        rw [List.getElem_drop]
        have : d + (i - d) = i := by omega
        simp [this, hrb_i]
      have hdj_val : (rb.drop d)[j - d]'hj_d = v := by
        rw [List.getElem_drop]
        have : d + (j - d) = j := by omega
        simp [this, hrb_j]
      rw [hdi_val, hdj_val] at hM₀_b
      rw [← hra_drop] at hM₀_a
      refine Or.inr ⟨pairwise_phiStep d rb, pairwise_phiStep d ra,
        (((rb.take d).map (· - 1) : List ℕ) : Multiset ℕ) + M₀, u, v, hvu, hv1, ?_, ?_⟩
      · rw [coe_phiStep, ← Multiset.coe_add, hM₀_b, Multiset.add_cons, Multiset.add_cons]
      · rw [coe_phiStep, ← Multiset.coe_add, hra_take, hM₀_a, Multiset.add_cons, Multiset.add_cons]
    · -- i < d ≤ j
      have hid : i < d := Nat.lt_of_not_ge hdi
      have hdj : d ≤ j := Nat.le_of_not_lt hjd
      have hra_take : ra.take d = (rb.take d).set i (u + 1) := by
        rw [hra_eq, take_set_of_ge _ hdj, take_set_of_lt _ hid]
      have hra_drop : ra.drop d = (rb.drop d).set (j - d) (v - 1) := by
        rw [hra_eq, drop_set_of_ge _ hdj, drop_set_of_lt _ hid]
      have hi_t : i < (rb.take d).length := by rw [List.length_take_of_le hd]; exact hid
      have hi_m : i < ((rb.take d).map (· - 1)).length := by rw [List.length_map]; exact hi_t
      have hmi : ((rb.take d).map (· - 1))[i]'hi_m = u - 1 := by simp [List.getElem_take, hrb_i]
      have hmem_m : u - 1 ∈ (((rb.take d).map (· - 1) : List ℕ) : Multiset ℕ) := by
        rw [Multiset.mem_coe, ← hmi]; exact List.getElem_mem hi_m
      obtain ⟨M₁, hM₁_b⟩ := Multiset.exists_cons_of_mem hmem_m
      have hM₁_a : (((ra.take d).map (· - 1) : List ℕ) : Multiset ℕ) = u ::ₘ M₁ := by
        have hmap : (ra.take d).map (· - 1) = ((rb.take d).map (· - 1)).set i u := by
          rw [hra_take, List.map_set]
          have : (u + 1) - 1 = u := by omega
          rw [this]
        rw [hmap]
        exact coe_set_eq_of_coe_cons hi_m hmi hM₁_b
      have hj_d : j - d < (rb.drop d).length := by rw [List.length_drop]; omega
      have hdj_val : (rb.drop d)[j - d]'hj_d = v := by
        rw [List.getElem_drop]
        have : d + (j - d) = j := by omega
        simp [this, hrb_j]
      have hmem_d : v ∈ (rb.drop d : Multiset ℕ) := by
        rw [Multiset.mem_coe, ← hdj_val]; exact List.getElem_mem hj_d
      obtain ⟨M₂, hM₂_b⟩ := Multiset.exists_cons_of_mem hmem_d
      have hM₂_a : (ra.drop d : Multiset ℕ) = (v - 1) ::ₘ M₂ := by
        rw [hra_drop]
        exact coe_set_eq_of_coe_cons hj_d hdj_val hM₂_b
      have hb'_coe : (phiStep d rb : Multiset ℕ) = (u - 1) ::ₘ v ::ₘ (M₁ + M₂) := by
        rw [coe_phiStep, ← Multiset.coe_add, hM₁_b, hM₂_b, Multiset.cons_add, Multiset.add_cons]
      have ha'_coe : (phiStep d ra : Multiset ℕ) = u ::ₘ (v - 1) ::ₘ (M₁ + M₂) := by
        rw [coe_phiStep, ← Multiset.coe_add, hM₁_a, hM₂_a, Multiset.cons_add, Multiset.add_cons]
      rcases Nat.eq_or_lt_of_le hvu with rfl | hlt
      · refine Or.inl (eq_of_coe_eq_of_pairwise (pairwise_phiStep d rb) (pairwise_phiStep d ra) ?_)
        rw [hb'_coe, ha'_coe, Multiset.cons_swap]
      · refine Or.inr ⟨pairwise_phiStep d rb, pairwise_phiStep d ra,
          M₁ + M₂, u - 1, v, by omega, hv1, hb'_coe, ?_⟩
        rw [ha'_coe]
        have : (u - 1) + 1 = u := by omega
        rw [this]

/-! ## 3. Case A2: Raising Transfer Incrementing the Maximum `d` -/

private theorem exchangeStep_caseA2 {d v : ℕ} {rb ra : List ℕ} {m : Multiset ℕ}
    (hb_pw : (d :: rb).Pairwise (· ≥ ·))
    (ha_pw : ((d + 1) :: ra).Pairwise (· ≥ ·))
    (hVb : IsHHValid (d :: rb))
    (hVa : IsHHValid ((d + 1) :: ra))
    (hv1 : 1 ≤ v)
    (hrb_coe : (rb : Multiset ℕ) = v ::ₘ m)
    (hra_coe : (ra : Multiset ℕ) = (v - 1) ::ₘ m) :
    SafeDoubleDec (phiStep d rb) (phiStep (d + 1) ra) := by
  have hrb_pw : rb.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hb_pw).2
  have hra_pw : ra.Pairwise (· ≥ ·) := (List.pairwise_cons.mp ha_pw).2
  obtain ⟨hd_rb, hpos_rb, hVb'⟩ := (isHHValid_cons d rb).mp hVb
  obtain ⟨hd1_ra, hpos_ra, _⟩ := (isHHValid_cons (d + 1) ra).mp hVa
  have hlen_eq : ra.length = rb.length := length_eq_of_singleDec hrb_coe hra_coe
  have hd_lt : d < rb.length := by omega
  have hd_lt_ra : d < ra.length := by omega
  let b' := phiStep d rb
  let a' := phiStep (d + 1) ra
  have hb'_pw : b'.Pairwise (· ≥ ·) := pairwise_phiStep d rb
  have ha'_pw : a'.Pairwise (· ≥ ·) := pairwise_phiStep (d + 1) ra
  -- Establish `b' = d' :: rb'` with `1 ≤ d' ≤ rb'.length` and `d' ≤ d`
  have hsum_rb : rb.sum = ra.sum + 1 := by
    have h1 : rb.sum = (v ::ₘ m).sum := by rw [← hrb_coe, Multiset.sum_coe]
    have h2 : ra.sum = ((v - 1) ::ₘ m).sum := by rw [← hra_coe, Multiset.sum_coe]
    simp only [Multiset.sum_cons] at h1 h2
    omega
  have hsum_b' : b'.sum + d = rb.sum := sum_phiStep hd_rb hpos_rb
  have hsum_a' : a'.sum + (d + 1) = ra.sum := sum_phiStep hd1_ra hpos_ra
  have hb'_sum_pos : 0 < b'.sum := by omega
  obtain ⟨d', rb', hb'_eq, hd'1⟩ := exists_cons_pos_of_sum_pos hb'_pw hb'_sum_pos
  rw [havelHakimiStep_cons_eq_phiStep] at hVb'
  have hVb'_cons : IsHHValid (d' :: rb') := hb'_eq ▸ hVb'
  have hd'_le_len : d' ≤ rb'.length := ((isHHValid_cons d' rb').mp hVb'_cons).1
  have hd'_lt : d' < b'.length := by rw [hb'_eq, List.length_cons]; omega
  -- Every entry of `b'` is ≤ d, so `d' ≤ d`
  have hd'_le_d : d' ≤ d := by
    have hd'_mem : d' ∈ b' := by rw [hb'_eq]; simp
    rw [← Multiset.mem_coe, coe_phiStep, ← Multiset.coe_add, Multiset.mem_add,
        Multiset.mem_coe, Multiset.mem_coe] at hd'_mem
    rcases hd'_mem with h1 | h2
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h1
      have hz_rb : z ∈ rb := List.mem_of_mem_take hz
      have := le_head_of_pairwise_ge hb_pw hz_rb
      omega
    · have := le_head_of_pairwise_ge hb_pw (List.mem_of_mem_drop h2)
      omega
  -- Threshold bound: `rb[d] ≤ rb'.getD (d' - 1) 0 + 1`
  have hthresh : rb[d]'hd_lt ≤ rb'.getD (d' - 1) 0 + 1 := by
    have hcard_ge : d' + 1 ≤ ((b' : Multiset ℕ).filter (rb[d]'hd_lt - 1 ≤ ·)).card := by
      rw [coe_phiStep, ← Multiset.coe_add, Multiset.filter_add, Multiset.card_add]
      have htake_all :
          Multiset.filter (rb[d]'hd_lt - 1 ≤ ·)
            (((rb.take d).map (· - 1) : List ℕ) : Multiset ℕ) =
          (((rb.take d).map (· - 1) : List ℕ) : Multiset ℕ) := by
        rw [Multiset.filter_eq_self]
        intro z hz
        rw [Multiset.mem_coe] at hz
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
        have hk_d : k < d := by rw [List.length_take_of_le hd_rb] at hk; exact hk
        have hkeq : (rb.take d)[k]'hk = rb[k]'(by omega) := List.getElem_take
        rw [hkeq]
        have hle := getElem_ge_of_pairwise_ge hrb_pw (by omega : k < rb.length) hd_lt (by omega)
        omega
      have hcard_take :
          (Multiset.filter (rb[d]'hd_lt - 1 ≤ ·)
            (((rb.take d).map (· - 1) : List ℕ) : Multiset ℕ)).card = d := by
        rw [htake_all, Multiset.coe_card, List.length_map, List.length_take_of_le hd_rb]
      have hdrop_pos :
          1 ≤ (Multiset.filter (rb[d]'hd_lt - 1 ≤ ·) (rb.drop d : Multiset ℕ)).card := by
        have hmem_f : rb[d]'hd_lt ∈ Multiset.filter (rb[d]'hd_lt - 1 ≤ ·) (rb.drop d : Multiset ℕ) := by
          rw [Multiset.mem_filter, Multiset.mem_coe]
          refine ⟨?_, by omega⟩
          have h0 : 0 < (rb.drop d).length := by rw [List.length_drop]; omega
          have hget : (rb.drop d)[0]'h0 = rb[d]'hd_lt := by simp [List.getElem_drop]
          rw [← hget]
          exact List.getElem_mem h0
        obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hmem_f
        rw [ht, Multiset.card_cons]
        omega
      omega
    have hle := le_getElem_of_filter_card_ge hb'_pw hd'_lt hcard_ge
    have hidx_eq : b'[d']'hd'_lt = rb'.getD (d' - 1) 0 := by
      have hd'1_lt : d' - 1 < rb'.length := by omega
      rw [getD_eq_getElem_nat rb' hd'1_lt]
      cases d' with
      | zero => omega
      | succ k =>
        simp [hb'_eq]
    rw [hidx_eq] at hle
    omega
  -- Express `ra = rb.set j (v - 1)` and compare `b'` vs `a'` across `j < d`, `j = d`, `d < j`
  obtain ⟨j, hj, hrb_j, _, hra_set⟩ := eq_set_dec_last_of_singleDec hrb_pw hra_pw hrb_coe hra_coe
  obtain ⟨hb'_split, _⟩ := coe_phiStep_split_succ hd_lt
  obtain ⟨_, ha'_split⟩ := coe_phiStep_split_succ hd_lt_ra
  refine ⟨hb'_pw, ha'_pw, d', rb', hb'_eq, hd'1, hd'_le_len, ?_⟩
  by_cases hjd : j < d
  · -- Subcase j < d: two distinct entries `rb[d]` and `v - 1` decremented
    have hra_take : ra.take d = (rb.take d).set j (v - 1) := by
      rw [hra_set, take_set_of_lt rb hjd]
    have hra_d : ra[d]'hd_lt_ra = rb[d]'hd_lt := by
      simp [hra_set, Nat.ne_of_lt hjd]
    have hra_drop1 : ra.drop (d + 1) = rb.drop (d + 1) := by
      rw [hra_set, drop_set_of_lt rb (by omega)]
    have hrb_d_pos : 1 ≤ rb[d]'hd_lt := by
      have hmem : ra[d]'hd_lt_ra ∈ ra.take (d + 1) := by
        have hlen : d < (ra.take (d + 1)).length := by
          rw [List.length_take_of_le hd1_ra]; omega
        have hget : (ra.take (d + 1))[d]'hlen = ra[d]'hd_lt_ra := List.getElem_take
        rw [← hget]; exact List.getElem_mem hlen
      rw [hra_d] at hmem
      exact hpos_ra _ hmem
    have hv1_pos : 1 ≤ v - 1 := by
      have hmem : v - 1 ∈ ra.take (d + 1) := by
        have hlen : j < (ra.take (d + 1)).length := by
          rw [List.length_take_of_le hd1_ra]; omega
        have hget : (ra.take (d + 1))[j]'hlen = v - 1 := by
          rw [List.getElem_take]; simp [hra_set]
        rw [← hget]; exact List.getElem_mem hlen
      exact hpos_ra _ hmem
    have hj_t : j < (rb.take d).length := by rw [List.length_take_of_le hd_rb]; exact hjd
    have hj_m : j < ((rb.take d).map (· - 1)).length := by rw [List.length_map]; exact hj_t
    have hmj : ((rb.take d).map (· - 1))[j]'hj_m = v - 1 := by simp [List.getElem_take, hrb_j]
    have hmem_m : v - 1 ∈ (((rb.take d).map (· - 1) : List ℕ) : Multiset ℕ) := by
      rw [Multiset.mem_coe, ← hmj]; exact List.getElem_mem hj_m
    obtain ⟨M₀, hM₀_b⟩ := Multiset.exists_cons_of_mem hmem_m
    have hM₀_a : (((ra.take d).map (· - 1) : List ℕ) : Multiset ℕ) = (v - 1 - 1) ::ₘ M₀ := by
      rw [hra_take, List.map_set]
      exact coe_set_eq_of_coe_cons hj_m hmj hM₀_b
    have hb'_m : (b' : Multiset ℕ) = (v - 1) ::ₘ (rb[d]'hd_lt) ::ₘ (M₀ + (rb.drop (d + 1) : Multiset ℕ)) := by
      change (phiStep d rb : Multiset ℕ) = _
      rw [hb'_split, hM₀_b, Multiset.cons_add, Multiset.add_cons]
    have ha'_m : (a' : Multiset ℕ) =
        (v - 1 - 1) ::ₘ (rb[d]'hd_lt - 1) ::ₘ (M₀ + (rb.drop (d + 1) : Multiset ℕ)) := by
      change (phiStep (d + 1) ra : Multiset ℕ) = _
      rw [ha'_split, hM₀_a, hra_d, hra_drop1, Multiset.cons_add, Multiset.add_cons]
    refine Or.inl ?_
    by_cases hcmp : v - 1 ≤ rb[d]'hd_lt
    · refine ⟨M₀ + (rb.drop (d + 1) : Multiset ℕ), rb[d]'hd_lt, v - 1, hv1_pos, hcmp, by omega, ?_, ?_⟩
      · rw [hb'_m, Multiset.cons_swap]
      · rw [ha'_m, Multiset.cons_swap]
    · refine ⟨M₀ + (rb.drop (d + 1) : Multiset ℕ), v - 1, rb[d]'hd_lt, hrb_d_pos, by omega, hthresh,
        hb'_m, ha'_m⟩
  · by_cases hjeq : j = d
    · -- Subcase j = d: single entry `rb[d] = v` decremented twice
      subst hjeq
      have hra_take : ra.take j = rb.take j := by rw [hra_set, take_set_of_ge rb le_rfl]
      have hra_j : ra[j]'hd_lt_ra = v - 1 := by simp [hra_set]
      have hra_drop1 : ra.drop (j + 1) = rb.drop (j + 1) := by
        rw [hra_set, drop_set_of_lt rb (by omega)]
      have hv2 : 2 ≤ v := by
        have hmem : v - 1 ∈ ra.take (j + 1) := by
          have hlen : j < (ra.take (j + 1)).length := by
            rw [List.length_take_of_le hd1_ra]; omega
          have hget : (ra.take (j + 1))[j]'hlen = v - 1 := by
            rw [List.getElem_take]; exact hra_j
          rw [← hget]; exact List.getElem_mem hlen
        have := hpos_ra _ hmem
        omega
      refine Or.inr ⟨(((rb.take j).map (· - 1) : List ℕ) : Multiset ℕ) + (rb.drop (j + 1) : Multiset ℕ),
        v, hv2, hrb_j ▸ hthresh, ?_, ?_⟩
      · rw [hb'_split, hrb_j, Multiset.add_cons]
      · rw [ha'_split, hra_take, hra_j, hra_drop1, Multiset.add_cons]
        have : (v - 1) - 1 = v - 2 := by omega
        rw [this]
    · -- Subcase d < j: two distinct entries `rb[d]` and `v = rb[j]` decremented
      have hdj : d < j := by omega
      have hra_take : ra.take d = rb.take d := by rw [hra_set, take_set_of_ge rb (by omega)]
      have hra_d : ra[d]'hd_lt_ra = rb[d]'hd_lt := by
        simp [hra_set, Nat.ne_of_gt hdj]
      have hra_drop1 : ra.drop (d + 1) = (rb.drop (d + 1)).set (j - (d + 1)) (v - 1) := by
        rw [hra_set, drop_set_of_ge rb (by omega)]
      have hrb_d_pos : 1 ≤ rb[d]'hd_lt := by
        have hmem : ra[d]'hd_lt_ra ∈ ra.take (d + 1) := by
          have hlen : d < (ra.take (d + 1)).length := by
            rw [List.length_take_of_le hd1_ra]; omega
          have hget : (ra.take (d + 1))[d]'hlen = ra[d]'hd_lt_ra := List.getElem_take
          rw [← hget]; exact List.getElem_mem hlen
        rw [hra_d] at hmem
        exact hpos_ra _ hmem
      have hv_le_rbd : v ≤ rb[d]'hd_lt := by
        rw [← hrb_j]
        exact getElem_ge_of_pairwise_ge hrb_pw hd_lt hj (by omega)
      have hj_d1 : j - (d + 1) < (rb.drop (d + 1)).length := by rw [List.length_drop]; omega
      have hval_j : (rb.drop (d + 1))[j - (d + 1)]'hj_d1 = v := by
        rw [List.getElem_drop]
        have : (d + 1) + (j - (d + 1)) = j := by omega
        simp [this, hrb_j]
      have hmem_d1 : v ∈ (rb.drop (d + 1) : Multiset ℕ) := by
        rw [Multiset.mem_coe, ← hval_j]; exact List.getElem_mem hj_d1
      obtain ⟨M₀, hM₀_b⟩ := Multiset.exists_cons_of_mem hmem_d1
      have hM₀_a : (ra.drop (d + 1) : Multiset ℕ) = (v - 1) ::ₘ M₀ := by
        rw [hra_drop1]
        exact coe_set_eq_of_coe_cons hj_d1 hval_j hM₀_b
      refine Or.inl ⟨(((rb.take d).map (· - 1) : List ℕ) : Multiset ℕ) + M₀,
        rb[d]'hd_lt, v, hv1, hv_le_rbd, by omega, ?_, ?_⟩
      · rw [hb'_split, hM₀_b, Multiset.add_cons, Multiset.add_cons]
      · rw [ha'_split, hra_take, hra_d, hM₀_a, Multiset.add_cons, Multiset.add_cons]

/-! ## 4. Case B1: Safe Double-Decrement Dropping the Maximum by `1` -/

private theorem exists_replicate_append_of_le (l : List ℕ) (v : ℕ)
    (hl : l.Pairwise (· ≥ ·)) (hle : ∀ z ∈ l, z ≤ v) :
    ∃ (k : ℕ) (tail : List ℕ),
      l = List.replicate k v ++ tail ∧ tail.Pairwise (· ≥ ·) ∧ ∀ z ∈ tail, z < v := by
  induction l with
  | nil => exact ⟨0, [], rfl, List.Pairwise.nil, fun _ h => nomatch h⟩
  | cons a t ih =>
    have ⟨ha_ge, ht_pw⟩ := List.pairwise_cons.mp hl
    have ha_le : a ≤ v := hle a (by simp)
    by_cases hav : a = v
    · subst hav
      obtain ⟨k, tail, hsplit, htpw, htle⟩ := ih ht_pw (fun z hz => hle z (by simp [hz]))
      exact ⟨k + 1, tail, by simp [List.replicate_succ, hsplit], htpw, htle⟩
    · refine ⟨0, a :: t, rfl, hl, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hzt
      · omega
      · have := ha_ge z hzt; omega

private theorem safeDoubleDec_caseB1a {d : ℕ} {rb ra : List ℕ}
    (hrb_pw : rb.Pairwise (· ≥ ·))
    (hra_pw : ra.Pairwise (· ≥ ·))
    (hd2 : 2 ≤ d) (hd_rb : d ≤ rb.length)
    (hrb_le : ∀ z ∈ rb, z ≤ d - 1)
    (hsafe : d ≤ rb.getD (d - 1) 0 + 1)
    (hra_coe : (d - 1) ::ₘ (ra : Multiset ℕ) = (d - 2) ::ₘ (rb : Multiset ℕ)) :
    phiStep d rb = phiStep (d - 1) ra := by
  have hd1_lt : d - 1 < rb.length := by omega
  have hrb_d1 : rb[d - 1]'hd1_lt = d - 1 := by
    rw [getD_eq_getElem_nat rb hd1_lt] at hsafe
    have hle := hrb_le _ (List.getElem_mem hd1_lt)
    omega
  have htake_rb : rb.take d = List.replicate d (d - 1) := by
    apply List.ext_getElem
    · rw [List.length_take_of_le hd_rb, List.length_replicate]
    · intro k hk1 hk2
      rw [List.length_take_of_le hd_rb] at hk1
      rw [List.getElem_take, List.getElem_replicate]
      have hge := getElem_ge_of_pairwise_ge hrb_pw (by omega : k < rb.length) hd1_lt (by omega)
      have hle := hrb_le _ (List.getElem_mem (by omega : k < rb.length))
      omega
  -- Split `rb.drop d` into copies of `d - 1` and tail (all ≤ d - 2)
  obtain ⟨k, tail, hdrop_split, htail_pw, htail_lt⟩ :=
    exists_replicate_append_of_le (rb.drop d) (d - 1) hrb_pw.drop
      (fun z hz => hrb_le z (List.mem_of_mem_drop hz))
  have hrb_decomp : rb = List.replicate (d + k) (d - 1) ++ tail := by
    rw [← List.take_append_drop d rb, htake_rb, hdrop_split, ← List.append_assoc,
        ← List.replicate_add]
  have htail_le : ∀ z ∈ tail, z ≤ d - 2 := fun z hz => by
    have := htail_lt z hz; omega
  -- Construct `ra` explicitly
  have hra_exact : ra = List.replicate (d - 1 + k) (d - 1) ++ ((d - 2) :: tail) := by
    have hpw_rhs : (List.replicate (d - 1 + k) (d - 1) ++ ((d - 2) :: tail)).Pairwise (· ≥ ·) := by
      rw [List.pairwise_append]
      refine ⟨List.pairwise_replicate.mpr (Or.inr le_rfl), ?_, ?_⟩
      · rw [List.pairwise_cons]
        exact ⟨fun z hz => htail_le z hz, htail_pw⟩
      · intro x hx y hy
        have hx' : x = d - 1 := List.eq_of_mem_replicate hx
        subst hx'
        rcases List.mem_cons.mp hy with rfl | hz
        · omega
        · have := htail_le y hz; omega
    have hcoe_rhs :
        (d - 1) ::ₘ ((List.replicate (d - 1 + k) (d - 1) ++ ((d - 2) :: tail) : List ℕ) : Multiset ℕ) =
          (d - 2) ::ₘ (rb : Multiset ℕ) := by
      rw [hrb_decomp]
      have hdk : d + k = (d - 1 + k) + 1 := by omega
      rw [hdk, List.replicate_succ]
      simp only [← Multiset.coe_add]
      change (d - 1) ::ₘ ((List.replicate (d - 1 + k) (d - 1) : List ℕ) : Multiset ℕ) +
          ((d - 2) ::ₘ (tail : Multiset ℕ)) =
        (d - 2) ::ₘ (((d - 1) ::ₘ ((List.replicate (d - 1 + k) (d - 1) : List ℕ) : Multiset ℕ)) +
          (tail : Multiset ℕ))
      rw [Multiset.cons_add, Multiset.add_cons, Multiset.cons_add, Multiset.cons_swap]
    have hcoe_eq : (ra : Multiset ℕ) =
        ((List.replicate (d - 1 + k) (d - 1) ++ ((d - 2) :: tail) : List ℕ) : Multiset ℕ) :=
      (Multiset.cons_inj_right (d - 1)).mp (hra_coe.trans hcoe_rhs.symm)
    exact eq_of_coe_eq_of_pairwise hra_pw hpw_rhs hcoe_eq
  -- Compute `phiStep d rb` and `phiStep (d - 1) ra` multisets and show equality
  apply eq_of_coe_eq_of_pairwise (pairwise_phiStep d rb) (pairwise_phiStep (d - 1) ra)
  rw [coe_phiStep, coe_phiStep]
  have hrb_drop_eq : rb.drop d = List.replicate k (d - 1) ++ tail := hdrop_split
  have hra_take : ra.take (d - 1) = List.replicate (d - 1) (d - 1) := by
    rw [hra_exact, List.replicate_add, List.append_assoc, List.take_left' (by simp)]
  have hra_drop : ra.drop (d - 1) = List.replicate k (d - 1) ++ ((d - 2) :: tail) := by
    rw [hra_exact, List.replicate_add, List.append_assoc, List.drop_left' (by simp)]
  rw [htake_rb, hrb_drop_eq, hra_take, hra_drop]
  simp only [List.map_replicate, ← Multiset.coe_add]
  have hd_succ : d = (d - 1) + 1 := by omega
  conv_lhs => rw [hd_succ, List.replicate_succ]
  have hsub : d - 1 - 1 = d - 2 := by omega
  rw [hsub]
  change ((d - 2) ::ₘ ((List.replicate (d - 1) (d - 2) : List ℕ) : Multiset ℕ)) +
      (((List.replicate k (d - 1) : List ℕ) : Multiset ℕ) + (tail : Multiset ℕ)) =
    ((List.replicate (d - 1) (d - 2) : List ℕ) : Multiset ℕ) +
      (((List.replicate k (d - 1) : List ℕ) : Multiset ℕ) + ((d - 2) ::ₘ (tail : Multiset ℕ)))
  rw [Multiset.cons_add, Multiset.add_cons, Multiset.add_cons]

private theorem safeDoubleDec_caseB1b {d y : ℕ} {rb ra : List ℕ} {m : Multiset ℕ}
    (hrb_pw : rb.Pairwise (· ≥ ·))
    (hra_pw : ra.Pairwise (· ≥ ·))
    (hd2 : 2 ≤ d) (hd_rb : d ≤ rb.length)
    (hy1 : 1 ≤ y) (hsafe : y ≤ rb.getD (d - 1) 0 + 1)
    (hpos_ra : ∀ z ∈ ra.take (d - 1), 1 ≤ z)
    (hrb_coe : (rb : Multiset ℕ) = y ::ₘ m)
    (hra_coe : (ra : Multiset ℕ) = (y - 1) ::ₘ m) :
    phiStep d rb = phiStep (d - 1) ra ∨ ExchangeStep (phiStep d rb) (phiStep (d - 1) ra) := by
  have hd0 : d - 1 < rb.length := by omega
  have hlen : ra.length = rb.length := length_eq_of_singleDec hrb_coe hra_coe
  have hd0_ra : d - 1 < ra.length := by omega
  obtain ⟨q, hq, hrb_q, hlast, hra_set⟩ := eq_set_dec_last_of_singleDec hrb_pw hra_pw hrb_coe hra_coe
  have hdd : (d - 1) + 1 = d := by omega
  obtain ⟨_, hb'_split⟩ := coe_phiStep_split_succ hd0
  obtain ⟨ha'_split, _⟩ := coe_phiStep_split_succ hd0_ra
  rw [hdd] at hb'_split ha'_split
  by_cases hq_eq : q = d - 1
  · -- q = d - 1: exact same multiset
    subst hq_eq
    refine Or.inl (eq_of_coe_eq_of_pairwise (pairwise_phiStep d rb) (pairwise_phiStep (d - 1) ra) ?_)
    have hra_take : ra.take (d - 1) = rb.take (d - 1) := by
      rw [hra_set, take_set_of_ge rb le_rfl]
    have hra_q : ra[d - 1]'hd0_ra = y - 1 := by simp [hra_set]
    have hra_drop : ra.drop d = rb.drop d := by rw [hra_set, drop_set_of_lt rb (by omega)]
    rw [hb'_split, ha'_split, hra_take, hra_q, hra_drop, hrb_q]
  · by_cases hqd : d - 1 < q
    · -- d - 1 < q: indices {d - 1, q}
      have hra_take : ra.take (d - 1) = rb.take (d - 1) := by
        rw [hra_set, take_set_of_ge rb (by omega)]
      have hra_d0 : ra[d - 1]'hd0_ra = rb[d - 1]'hd0 := by
        simp [hra_set, Nat.ne_of_gt hqd]
      have hra_drop : ra.drop d = (rb.drop d).set (q - d) (y - 1) := by
        rw [hra_set, drop_set_of_ge rb (by omega)]
      have hq_d : q - d < (rb.drop d).length := by rw [List.length_drop]; omega
      have hval_q : (rb.drop d)[q - d]'hq_d = y := by
        rw [List.getElem_drop]
        have : d + (q - d) = q := by omega
        simp [this, hrb_q]
      have hmem_d : y ∈ (rb.drop d : Multiset ℕ) := by
        rw [Multiset.mem_coe, ← hval_q]; exact List.getElem_mem hq_d
      obtain ⟨M₀, hM₀_b⟩ := Multiset.exists_cons_of_mem hmem_d
      have hM₀_a : (ra.drop d : Multiset ℕ) = (y - 1) ::ₘ M₀ := by
        rw [hra_drop]
        exact coe_set_eq_of_coe_cons hq_d hval_q hM₀_b
      have hb'_m : (phiStep d rb : Multiset ℕ) =
          (rb[d - 1]'hd0 - 1) ::ₘ y ::ₘ
            ((((rb.take (d - 1)).map (· - 1) : List ℕ) : Multiset ℕ) + M₀) := by
        rw [hb'_split, hM₀_b, Multiset.add_cons, Multiset.add_cons]
      have ha'_m : (phiStep (d - 1) ra : Multiset ℕ) =
          (rb[d - 1]'hd0) ::ₘ (y - 1) ::ₘ
            ((((rb.take (d - 1)).map (· - 1) : List ℕ) : Multiset ℕ) + M₀) := by
        rw [ha'_split, hra_take, hra_d0, hM₀_a, Multiset.add_cons, Multiset.add_cons]
      have hy_le : y ≤ rb[d - 1]'hd0 := by
        rw [← hrb_q]
        exact getElem_ge_of_pairwise_ge hrb_pw hd0 hq (by omega)
      rcases Nat.eq_or_lt_of_le hy_le with heq | hlt
      · refine Or.inl (eq_of_coe_eq_of_pairwise (pairwise_phiStep d rb)
            (pairwise_phiStep (d - 1) ra) ?_)
        rw [hb'_m, ha'_m, heq, Multiset.cons_swap]
      · refine Or.inr ⟨pairwise_phiStep d rb, pairwise_phiStep (d - 1) ra,
          (((rb.take (d - 1)).map (· - 1) : List ℕ) : Multiset ℕ) + M₀,
          rb[d - 1]'hd0 - 1, y, by omega, hy1, hb'_m, ?_⟩
        rw [ha'_m]
        have : (rb[d - 1]'hd0 - 1) + 1 = rb[d - 1]'hd0 := by omega
        rw [this]
    · -- q < d - 1: y = rb[d - 1] + 1, exact multiset swap giving equality
      have hq_lt : q < d - 1 := by omega
      have hrb_d0_lt : rb[d - 1]'hd0 < y := hlast (d - 1) hq_lt hd0
      rw [getD_eq_getElem_nat rb hd0] at hsafe
      have hrb_d0_eq : rb[d - 1]'hd0 = y - 1 := by omega
      have hra_take : ra.take (d - 1) = (rb.take (d - 1)).set q (y - 1) := by
        rw [hra_set, take_set_of_lt rb hq_lt]
      have hra_d0 : ra[d - 1]'hd0_ra = y - 1 := by
        simp [hra_set, Nat.ne_of_lt hq_lt, hrb_d0_eq]
      have hra_drop : ra.drop d = rb.drop d := by
        rw [hra_set, drop_set_of_lt rb (by omega)]
      have hq_t : q < (rb.take (d - 1)).length := by
        rw [List.length_take_of_le (by omega)]; exact hq_lt
      have hq_m : q < ((rb.take (d - 1)).map (· - 1)).length := by rw [List.length_map]; exact hq_t
      have hmq : ((rb.take (d - 1)).map (· - 1))[q]'hq_m = y - 1 := by
        simp [List.getElem_take, hrb_q]
      have hmem_m : y - 1 ∈ (((rb.take (d - 1)).map (· - 1) : List ℕ) : Multiset ℕ) := by
        rw [Multiset.mem_coe, ← hmq]; exact List.getElem_mem hq_m
      obtain ⟨M₀, hM₀_b⟩ := Multiset.exists_cons_of_mem hmem_m
      have hM₀_a : (((ra.take (d - 1)).map (· - 1) : List ℕ) : Multiset ℕ) = (y - 1 - 1) ::ₘ M₀ := by
        rw [hra_take, List.map_set]
        exact coe_set_eq_of_coe_cons hq_m hmq hM₀_b
      have _ := hpos_ra
      refine Or.inl (eq_of_coe_eq_of_pairwise (pairwise_phiStep d rb)
          (pairwise_phiStep (d - 1) ra) ?_)
      rw [hb'_split, ha'_split, hM₀_b, hM₀_a, hrb_d0_eq, hra_d0, hra_drop]
      rw [Multiset.cons_add, Multiset.add_cons, Multiset.cons_add, Multiset.add_cons,
          Multiset.cons_swap]

/-! ## 5. Case B2: Safe Double-Decrement Preserving the Maximum `d` -/

private theorem safeDoubleDec_caseB2 {d : ℕ} {rb ra : List ℕ}
    (hb_pw : (d :: rb).Pairwise (· ≥ ·))
    (ha_pw : (d :: ra).Pairwise (· ≥ ·))
    (hVb : IsHHValid (d :: rb))
    (hVa : IsHHValid (d :: ra))
    (hd1 : 1 ≤ d)
    (hdec :
      (∃ (m : Multiset ℕ) (x y : ℕ),
          1 ≤ y ∧ y ≤ x ∧ y ≤ rb.getD (d - 1) 0 + 1 ∧
          (rb : Multiset ℕ) = x ::ₘ y ::ₘ m ∧
          (ra : Multiset ℕ) = (x - 1) ::ₘ (y - 1) ::ₘ m) ∨
      (∃ (m : Multiset ℕ) (x : ℕ),
          2 ≤ x ∧ x ≤ rb.getD (d - 1) 0 + 1 ∧
          (rb : Multiset ℕ) = x ::ₘ m ∧
          (ra : Multiset ℕ) = (x - 2) ::ₘ m)) :
    SafeDoubleDec (phiStep d rb) (phiStep d ra) := by
  have hrb_pw : rb.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hb_pw).2
  have hra_pw : ra.Pairwise (· ≥ ·) := (List.pairwise_cons.mp ha_pw).2
  obtain ⟨hd_rb, hpos_rb, hVb'⟩ := (isHHValid_cons d rb).mp hVb
  obtain ⟨hd_ra, hpos_ra, _⟩ := (isHHValid_cons d ra).mp hVa
  have hd1_lt : d - 1 < rb.length := by omega
  let b' := phiStep d rb
  let a' := phiStep d ra
  have hb'_pw : b'.Pairwise (· ≥ ·) := pairwise_phiStep d rb
  have ha'_pw : a'.Pairwise (· ≥ ·) := pairwise_phiStep d ra
  -- Show `rb.sum = ra.sum + 2` and `ra.length = rb.length`
  have hsum_diff : rb.sum = ra.sum + 2 := by
    rcases hdec with ⟨m, x, y, hy1, hyx, _, hrb_m, hra_m⟩ | ⟨m, x, hx2, _, hrb_m, hra_m⟩
    · have h1 : rb.sum = (x ::ₘ y ::ₘ m).sum := by rw [← hrb_m, Multiset.sum_coe]
      have h2 : ra.sum = ((x - 1) ::ₘ (y - 1) ::ₘ m).sum := by rw [← hra_m, Multiset.sum_coe]
      simp only [Multiset.sum_cons] at h1 h2; omega
    · have h1 : rb.sum = (x ::ₘ m).sum := by rw [← hrb_m, Multiset.sum_coe]
      have h2 : ra.sum = ((x - 2) ::ₘ m).sum := by rw [← hra_m, Multiset.sum_coe]
      simp only [Multiset.sum_cons] at h1 h2; omega
  have hsum_b' : b'.sum + d = rb.sum := sum_phiStep hd_rb hpos_rb
  have hsum_a' : a'.sum + d = ra.sum := sum_phiStep hd_ra hpos_ra
  have hb'_sum_pos : 0 < b'.sum := by omega
  obtain ⟨d', rb', hb'_eq, hd'1⟩ := exists_cons_pos_of_sum_pos hb'_pw hb'_sum_pos
  rw [havelHakimiStep_cons_eq_phiStep] at hVb'
  have hVb'_cons : IsHHValid (d' :: rb') := hb'_eq ▸ hVb'
  have hd'_le_len : d' ≤ rb'.length := ((isHHValid_cons d' rb').mp hVb'_cons).1
  have hd'_lt : d' < b'.length := by rw [hb'_eq, List.length_cons]; omega
  -- Every entry of `b'` is ≤ d, so `d' ≤ d`
  have hd'_le_d : d' ≤ d := by
    have hd'_mem : d' ∈ b' := by rw [hb'_eq]; simp
    rw [← Multiset.mem_coe, coe_phiStep, ← Multiset.coe_add, Multiset.mem_add,
        Multiset.mem_coe, Multiset.mem_coe] at hd'_mem
    rcases hd'_mem with h1 | h2
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h1
      have := le_head_of_pairwise_ge hb_pw (List.mem_of_mem_take hz)
      omega
    · exact le_head_of_pairwise_ge hb_pw (List.mem_of_mem_drop h2)
  -- Threshold bound: `rb[d - 1] ≤ rb'.getD (d' - 1) 0 + 1`
  have hthresh : rb[d - 1]'hd1_lt ≤ rb'.getD (d' - 1) 0 + 1 := by
    have htake_all :
        Multiset.filter (rb[d - 1]'hd1_lt - 1 ≤ ·)
          (((rb.take d).map (· - 1) : List ℕ) : Multiset ℕ) =
        (((rb.take d).map (· - 1) : List ℕ) : Multiset ℕ) := by
      rw [Multiset.filter_eq_self]
      intro z hz
      rw [Multiset.mem_coe] at hz
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu
      have hk_d : k < d := by rw [List.length_take_of_le hd_rb] at hk; exact hk
      have hkeq : (rb.take d)[k]'hk = rb[k]'(by omega) := List.getElem_take
      rw [hkeq]
      have hle := getElem_ge_of_pairwise_ge hrb_pw (by omega : k < rb.length) hd1_lt (by omega)
      omega
    have hcard_take :
        (Multiset.filter (rb[d - 1]'hd1_lt - 1 ≤ ·)
          (((rb.take d).map (· - 1) : List ℕ) : Multiset ℕ)).card = d := by
      rw [htake_all, Multiset.coe_card, List.length_map, List.length_take_of_le hd_rb]
    have hcard_ge : d' + 1 ≤ ((b' : Multiset ℕ).filter (rb[d - 1]'hd1_lt - 1 ≤ ·)).card := by
      rw [coe_phiStep, ← Multiset.coe_add, Multiset.filter_add, Multiset.card_add, hcard_take]
      rcases Nat.eq_or_lt_of_le hd'_le_d with heq | hlt
      · -- d' = d: d ∈ rb.drop d, so `rb[d - 1] = d` and `rb.drop d` contributes ≥ 1 element ≥ d - 1
        have hd_in_drop : d ∈ rb.drop d := by
          have hd_mem : d ∈ b' := by rw [hb'_eq, heq]; simp
          rw [← Multiset.mem_coe, coe_phiStep, ← Multiset.coe_add, Multiset.mem_add,
              Multiset.mem_coe, Multiset.mem_coe] at hd_mem
          rcases hd_mem with h1 | h2
          · obtain ⟨z, hz, hz_eq⟩ := List.mem_map.mp h1
            have := le_head_of_pairwise_ge hb_pw (List.mem_of_mem_take hz)
            omega
          · exact h2
        have hdrop_pos :
            1 ≤ (Multiset.filter (rb[d - 1]'hd1_lt - 1 ≤ ·) (rb.drop d : Multiset ℕ)).card := by
          have hmem_f : d ∈ Multiset.filter (rb[d - 1]'hd1_lt - 1 ≤ ·) (rb.drop d : Multiset ℕ) := by
            rw [Multiset.mem_filter, Multiset.mem_coe]
            refine ⟨hd_in_drop, ?_⟩
            have := le_head_of_pairwise_ge hb_pw (List.getElem_mem hd1_lt)
            omega
          obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hmem_f
          rw [ht, Multiset.card_cons]
          omega
        omega
      · omega
    have hle := le_getElem_of_filter_card_ge hb'_pw hd'_lt hcard_ge
    have hidx_eq : b'[d']'hd'_lt = rb'.getD (d' - 1) 0 := by
      have hd'1_lt : d' - 1 < rb'.length := by omega
      rw [getD_eq_getElem_nat rb' hd'1_lt]
      cases d' with
      | zero => omega
      | succ k => simp [hb'_eq]
    rw [hidx_eq] at hle
    omega
  -- Construct intermediate sorted list `M_mid` and apply `phiStep_singleDec` twice
  -- Unify the two branches of `hdec` into `(x, v₂, R₁, R₂)` with `rb = x ::ₘ R₁`, `M_mid = (x - 1) ::ₘ R₁ = v₂ ::ₘ R₂`, `ra = (v₂ - 1) ::ₘ R₂`
  have htwo_steps :
      ∃ (M_mid : List ℕ) (x v₂ : ℕ) (R₁ R₂ : Multiset ℕ),
        M_mid.Pairwise (· ≥ ·) ∧
        1 ≤ x ∧ 1 ≤ v₂ ∧
        v₂ ≤ rb[d - 1]'hd1_lt + 1 ∧
        (rb : Multiset ℕ) = x ::ₘ R₁ ∧
        (M_mid : Multiset ℕ) = (x - 1) ::ₘ R₁ ∧
        (M_mid : Multiset ℕ) = v₂ ::ₘ R₂ ∧
        (ra : Multiset ℕ) = (v₂ - 1) ::ₘ R₂ ∧
        (x ≤ rb[d - 1]'hd1_lt + 1 ∨ v₂ ∈ rb) := by
    rcases hdec with ⟨m, x, y, hy1, hyx, hysafe, hrb_m, hra_m⟩ | ⟨m, x, hx2, hxsafe, hrb_m, hra_m⟩
    · rw [getD_eq_getElem_nat rb hd1_lt] at hysafe
      let M_mid := ((x - 1) ::ₘ y ::ₘ m).sort (· ≥ ·)
      have hmid_pw : M_mid.Pairwise (· ≥ ·) := Multiset.pairwise_sort _ _
      have hmid_coe : (M_mid : Multiset ℕ) = (x - 1) ::ₘ y ::ₘ m := Multiset.sort_eq _ _
      refine ⟨M_mid, x, y, y ::ₘ m, (x - 1) ::ₘ m, hmid_pw, by omega, hy1, hysafe,
        hrb_m, hmid_coe, ?_, ?_, Or.inr ?_⟩
      · rw [hmid_coe, Multiset.cons_swap]
      · rw [hra_m, Multiset.cons_swap]
      · rw [← Multiset.mem_coe, hrb_m]
        exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self y m)
    · rw [getD_eq_getElem_nat rb hd1_lt] at hxsafe
      let M_mid := ((x - 1) ::ₘ m).sort (· ≥ ·)
      have hmid_pw : M_mid.Pairwise (· ≥ ·) := Multiset.pairwise_sort _ _
      have hmid_coe : (M_mid : Multiset ℕ) = (x - 1) ::ₘ m := Multiset.sort_eq _ _
      refine ⟨M_mid, x, x - 1, m, m, hmid_pw, by omega, by omega, by omega,
        hrb_m, hmid_coe, hmid_coe, ?_, Or.inl hxsafe⟩
      rw [hra_m]
      have : (x - 1) - 1 = x - 2 := by omega
      rw [this]
  obtain ⟨M_mid, x, v₂, R₁, R₂, hmid_pw, hx1, hv2_1, hv2_safe,
          hrb_R1, hmid_R1, hmid_R2, hra_R2, hx_or_v2⟩ := htwo_steps
  have hmid_len : M_mid.length = rb.length := length_eq_of_singleDec hrb_R1 hmid_R1
  have hpos_mid : ∀ z ∈ M_mid.take d, 1 ≤ z := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hz
    have hkd : k < d := by rw [List.length_take_of_le (by omega)] at hk; exact hk
    have hkeq : (M_mid.take d)[k]'hk = M_mid[k]'(by omega) := List.getElem_take
    rw [hkeq]
    have hle := getElem_le_of_singleDec hmid_pw hra_pw hmid_R2 hra_R2
      (by omega : k < M_mid.length) (by omega : k < ra.length)
    have hra_k_mem : ra[k]'(by omega) ∈ ra.take d := by
      have hk_t : k < (ra.take d).length := by rw [List.length_take_of_le hd_ra]; exact hkd
      have heq : (ra.take d)[k]'hk_t = ra[k]'(by omega) := List.getElem_take
      rw [← heq]; exact List.getElem_mem hk_t
    have := hpos_ra _ hra_k_mem
    omega
  -- Apply `phiStep_singleDec` to `rb → M_mid` and `M_mid → ra`
  obtain ⟨w₁, T₁, hw₁_pos, hb'_T1, hmid'_T1, hw₁_info⟩ :=
    phiStep_singleDec hrb_pw hmid_pw hd_rb hpos_mid hx1 hrb_R1 hmid_R1
  obtain ⟨w₂, T₂, hw₂_pos, hmid'_T2, ha'_T2, hw₂_info⟩ :=
    phiStep_singleDec hmid_pw hra_pw (by omega) hpos_ra hv2_1 hmid_R2 hra_R2
  -- Show `w₂ ≤ rb[d - 1]`
  have hw₂_le_rbd1 : w₂ ≤ rb[d - 1]'hd1_lt := by
    rcases hw₂_info with ⟨rfl, _⟩ | ⟨_, hw₂_getD, _⟩
    · omega
    · have hgetD_le : M_mid.getD d 0 ≤ rb.getD d 0 :=
        getD_le_of_singleDec hrb_pw hmid_pw hrb_R1 hmid_R1 d
      have hrb_d_le : rb.getD d 0 ≤ rb[d - 1]'hd1_lt := by
        by_cases hd_lt : d < rb.length
        · rw [getD_eq_getElem_nat rb hd_lt]
          exact getElem_ge_of_pairwise_ge hrb_pw hd1_lt hd_lt (by omega)
        · rw [getD_eq_zero_of_ge rb (Nat.le_of_not_lt hd_lt)]
          exact Nat.zero_le _
      omega
  refine ⟨hb'_pw, ha'_pw, d', rb', hb'_eq, hd'1, hd'_le_len, ?_⟩
  -- Compare `w₂` with `T₁` in `mid' = (w₁ - 1) ::ₘ T₁ = w₂ ::ₘ T₂`
  by_cases hw2_in : w₂ ∈ T₁
  · -- Distinct slots in `b'`
    obtain ⟨T₃, hT₃⟩ := Multiset.exists_cons_of_mem hw2_in
    have hT2_eq : T₂ = (w₁ - 1) ::ₘ T₃ := by
      have hEq : (w₁ - 1) ::ₘ T₁ = w₂ ::ₘ T₂ := hmid'_T1.symm.trans hmid'_T2
      rw [hT₃, Multiset.cons_swap] at hEq
      exact ((Multiset.cons_inj_right w₂).mp hEq).symm
    have hb'_m : (b' : Multiset ℕ) = w₁ ::ₘ w₂ ::ₘ T₃ := by
      change (phiStep d rb : Multiset ℕ) = _; rw [hb'_T1, hT₃]
    have ha'_m : (a' : Multiset ℕ) = (w₁ - 1) ::ₘ (w₂ - 1) ::ₘ T₃ := by
      change (phiStep d ra : Multiset ℕ) = _
      rw [ha'_T2, hT2_eq, Multiset.cons_swap]
    refine Or.inl ?_
    by_cases hcmp : w₂ ≤ w₁
    · exact ⟨T₃, w₁, w₂, hw₂_pos, hcmp, by omega, hb'_m, ha'_m⟩
    · refine ⟨T₃, w₂, w₁, hw₁_pos, by omega, by omega, ?_, ?_⟩
      · rw [hb'_m, Multiset.cons_swap]
      · rw [ha'_m, Multiset.cons_swap]
  · -- Same slot in `b'` decremented twice (`w₂ ∉ T₁`, so `w₂ = w₁ - 1` and `T₂ = T₁`)
    have hw2_mem_mid : w₂ ∈ (w₁ - 1) ::ₘ T₁ := by
      rw [← hmid'_T1, hmid'_T2]
      exact Multiset.mem_cons_self w₂ T₂
    have hw2_eq : w₂ = w₁ - 1 := by
      rcases Multiset.mem_cons.mp hw2_mem_mid with h | h
      · exact h
      · exact absurd h hw2_in
    have hT2_eq : T₂ = T₁ := by
      have hEq : (w₁ - 1) ::ₘ T₁ = w₂ ::ₘ T₂ := hmid'_T1.symm.trans hmid'_T2
      rw [hw2_eq] at hEq
      exact ((Multiset.cons_inj_right (w₁ - 1)).mp hEq).symm
    have hw₁_ge2 : 2 ≤ w₁ := by omega
    -- Show `w₁ ≤ rb[d - 1]` (rules out `w₁ = rb[d - 1] + 1`)
    have hw₁_le_rbd1 : w₁ ≤ rb[d - 1]'hd1_lt := by
      by_contra hgt
      have hw₁_eq : w₁ = rb[d - 1]'hd1_lt + 1 := by omega
      have hw₂_eq_rb : w₂ = rb[d - 1]'hd1_lt := by omega
      have hnotmem_b' : rb[d - 1]'hd1_lt ∉ b' := by
        intro hmem
        rw [← Multiset.mem_coe] at hmem
        change rb[d - 1]'hd1_lt ∈ (phiStep d rb : Multiset ℕ) at hmem
        rw [hb'_T1, Multiset.mem_cons] at hmem
        rcases hmem with heq | hmem_T1
        · omega
        · exact hw2_in (hw₂_eq_rb ▸ hmem_T1)
      -- From Step 1 (`hw₁_info`): right disjunct contradicts `w₁ = rb[d - 1] + 1`, so left holds!
      have hstep1 : w₁ = x - 1 ∧ M_mid.drop d = rb.drop d := by
        rcases hw₁_info with h1 | ⟨_, hw₁_le_d, _⟩
        · exact h1
        · have hrb_d_le : rb.getD d 0 ≤ rb[d - 1]'hd1_lt := by
            by_cases hd_lt : d < rb.length
            · rw [getD_eq_getElem_nat rb hd_lt]
              exact getElem_ge_of_pairwise_ge hrb_pw hd1_lt hd_lt (by omega)
            · rw [getD_eq_zero_of_ge rb (Nat.le_of_not_lt hd_lt)]
              exact Nat.zero_le _
          omega
      have hx_eq : x = rb[d - 1]'hd1_lt + 2 := by omega
      have hv2_in_rb : v₂ ∈ rb := by
        rcases hx_or_v2 with hx_le | hv2_mem
        · omega
        · exact hv2_mem
      -- From Step 2 (`hw₂_info`): both disjuncts imply `rb[d - 1] ∈ b'`, contradiction!
      rcases hw₂_info with ⟨hw₂_v2, _⟩ | ⟨hw₂_v2, _, hv2_drop⟩
      · -- `v₂ = rb[d - 1] + 1 ∈ rb`, hence `v₂ ∈ rb.take d`, so `rb[d - 1] ∈ b'`
        have hv2_eq : v₂ = rb[d - 1]'hd1_lt + 1 := by omega
        obtain ⟨k, hk, hrb_k⟩ := List.getElem_of_mem hv2_in_rb
        have hkd : k < d := by
          by_contra hge
          have hle := getElem_ge_of_pairwise_ge hrb_pw hd1_lt hk (by omega)
          omega
        have hk_t : k < (rb.take d).length := by rw [List.length_take_of_le hd_rb]; exact hkd
        have hv2_take : v₂ ∈ rb.take d := by
          have heq : (rb.take d)[k]'hk_t = v₂ := by rw [List.getElem_take]; exact hrb_k
          rw [← heq]; exact List.getElem_mem hk_t
        have hmem_b' : v₂ - 1 ∈ b' := mem_phiStep_of_mem_take hv2_take
        have : v₂ - 1 = rb[d - 1]'hd1_lt := by omega
        exact hnotmem_b' (this ▸ hmem_b')
      · -- `v₂ = rb[d - 1] ∈ M_mid.drop d = rb.drop d`, so `rb[d - 1] ∈ b'`
        rw [hstep1.2] at hv2_drop
        have hmem_b' : v₂ ∈ b' := mem_phiStep_of_mem_drop hv2_drop
        have : v₂ = rb[d - 1]'hd1_lt := by omega
        exact hnotmem_b' (this ▸ hmem_b')
    refine Or.inr ⟨T₁, w₁, hw₁_ge2, by omega, hb'_T1, ?_⟩
    rw [ha'_T2, hT2_eq, hw2_eq]
    have : (w₁ - 1) - 1 = w₁ - 2 := by omega
    rw [this]

/-! ## 6. Theorem 1: Simultaneous Strong Induction on List Length -/

private theorem residueAux_monotone_aux (n : ℕ) :
    (∀ b a : List ℕ, b.length = n → ExchangeStep b a → IsHHValid b → IsHHValid a →
      SimpleGraph.residueAux b ≤ SimpleGraph.residueAux a) ∧
    (∀ b a : List ℕ, b.length = n → SafeDoubleDec b a → IsHHValid b → IsHHValid a →
      SimpleGraph.residueAux b ≤ SimpleGraph.residueAux a) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    constructor
    · -- Part (A): Single elementary exchange step
      intro b a hlen hEx hVb hVa
      rcases hEx with ⟨hb_pw, ha_pw, m, u, v, hvu, hv1, hb_coe, ha_coe⟩
      cases b with
      | nil =>
        have : u ∈ ([] : List ℕ) := by
          rw [← Multiset.mem_coe, hb_coe]; exact Multiset.mem_cons_self u _
        cases this
      | cons d rb =>
        have hu_mem : u ∈ d :: rb := by
          rw [← Multiset.mem_coe, hb_coe]; exact Multiset.mem_cons_self u _
        have hu_le_d : u ≤ d := by
          rcases List.mem_cons.mp hu_mem with rfl | hmem
          · exact le_rfl
          · exact le_head_of_pairwise_ge hb_pw hmem
        have hd1 : 1 ≤ d := by omega
        rcases Nat.eq_or_lt_of_le hu_le_d with rfl | hu_lt_d
        · -- Case A2: `u = d`
          have hrb_coe : (rb : Multiset ℕ) = v ::ₘ m :=
            (Multiset.cons_inj_right u).mp hb_coe
          have hmax_a : ∀ z ∈ (v - 1) ::ₘ m, z ≤ u + 1 := by
            intro z hz
            rcases Multiset.mem_cons.mp hz with rfl | hzm
            · omega
            · have hz_rb : z ∈ rb := by
                rw [← Multiset.mem_coe, hrb_coe]; exact Multiset.mem_cons_of_mem hzm
              have := le_head_of_pairwise_ge hb_pw hz_rb
              omega
          obtain ⟨ra, rfl, _, hra_coe⟩ := head_eq_of_coe_cons_of_max ha_pw ha_coe hmax_a
          rw [residueAux_cons_pos hd1, residueAux_cons_pos (by omega),
              havelHakimiStep_cons_eq_phiStep, havelHakimiStep_cons_eq_phiStep]
          have hSafe := exchangeStep_caseA2 hb_pw ha_pw hVb hVa hv1 hrb_coe hra_coe
          have hVb' : IsHHValid (phiStep u rb) := by
            rw [← havelHakimiStep_cons_eq_phiStep]; exact isHHValid_havelHakimiStep hVb
          have hVa' : IsHHValid (phiStep (u + 1) ra) := by
            rw [← havelHakimiStep_cons_eq_phiStep]; exact isHHValid_havelHakimiStep hVa
          have hlen' : (phiStep u rb).length < n := by
            rw [length_phiStep]; simp at hlen; omega
          exact (ih _ hlen').2 _ _ rfl hSafe hVb' hVa'
        · -- Case A1: `u < d`
          have hd_in_m : d ∈ m := by
            have hd_mem : d ∈ u ::ₘ v ::ₘ m := by
              rw [← hb_coe, Multiset.mem_coe]; simp
            rcases Multiset.mem_cons.mp hd_mem with h1 | h2
            · omega
            · rcases Multiset.mem_cons.mp h2 with h3 | h4
              · omega
              · exact h4
          obtain ⟨m', rfl⟩ := Multiset.exists_cons_of_mem hd_in_m
          have hrb_coe : (rb : Multiset ℕ) = u ::ₘ v ::ₘ m' := by
            have : d ::ₘ (rb : Multiset ℕ) = d ::ₘ u ::ₘ v ::ₘ m' := by
              change ((d :: rb : List ℕ) : Multiset ℕ) = _
              rw [hb_coe, Multiset.cons_swap v d m', Multiset.cons_swap u d (v ::ₘ m')]
            exact (Multiset.cons_inj_right d).mp this
          have ha_coe' : (a : Multiset ℕ) = d ::ₘ (u + 1) ::ₘ (v - 1) ::ₘ m' := by
            rw [ha_coe, Multiset.cons_swap (v - 1) d m', Multiset.cons_swap (u + 1) d ((v - 1) ::ₘ m')]
          have hmax_a : ∀ z ∈ (u + 1) ::ₘ (v - 1) ::ₘ m', z ≤ d := by
            intro z hz
            rcases Multiset.mem_cons.mp hz with rfl | hz'
            · omega
            · rcases Multiset.mem_cons.mp hz' with rfl | hzm'
              · omega
              · have hz_rb : z ∈ rb := by
                  rw [← Multiset.mem_coe, hrb_coe]
                  exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hzm')
                exact le_head_of_pairwise_ge hb_pw hz_rb
          obtain ⟨ra, rfl, hra_pw, hra_coe⟩ := head_eq_of_coe_cons_of_max ha_pw ha_coe' hmax_a
          have hrb_pw : rb.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hb_pw).2
          obtain ⟨hd_rb, _, hVb'⟩ := (isHHValid_cons d rb).mp hVb
          obtain ⟨_, hpos_ra, hVa'⟩ := (isHHValid_cons d ra).mp hVa
          rw [residueAux_cons_pos hd1, residueAux_cons_pos hd1,
              havelHakimiStep_cons_eq_phiStep, havelHakimiStep_cons_eq_phiStep]
          rw [havelHakimiStep_cons_eq_phiStep] at hVb' hVa'
          have hEx_r : ExchangeStep rb ra :=
            ⟨hrb_pw, hra_pw, m', u, v, hvu, hv1, hrb_coe, hra_coe⟩
          rcases exchangeStep_caseA1 hEx_r hd_rb hpos_ra with heq | hEx'
          · rw [heq]
          · have hlen' : (phiStep d rb).length < n := by
              rw [length_phiStep]; simp at hlen; omega
            exact (ih _ hlen').1 _ _ rfl hEx' hVb' hVa'
    · -- Part (B): Safe double-decrement
      intro b a hlen hSafe hVb hVa
      rcases hSafe with ⟨hb_pw, ha_pw, d, rb, rfl, hd1, hd_rb, hdec⟩
      cases a with
      | nil =>
        have hlen_ab : (d :: rb).length = ([] : List ℕ).length := by
          rcases hdec with ⟨m, x, y, _, _, _, hbm, ham⟩ | ⟨m, x, _, _, hbm, ham⟩
          · have hc1 : (d :: rb).length = (x ::ₘ y ::ₘ m).card := by rw [← Multiset.coe_card, hbm]
            have hc2 : ([] : List ℕ).length = ((x - 1) ::ₘ (y - 1) ::ₘ m).card := by
              rw [← Multiset.coe_card, ham]
            simp only [Multiset.card_cons] at hc1 hc2; omega
          · have hc1 : (d :: rb).length = (x ::ₘ m).card := by rw [← Multiset.coe_card, hbm]
            have hc2 : ([] : List ℕ).length = ((x - 2) ::ₘ m).card := by
              rw [← Multiset.coe_card, ham]
            simp only [Multiset.card_cons] at hc1 hc2; omega
        simp at hlen_ab
      | cons d_a ra =>
        have hlen_eq : (d_a :: ra).length = (d :: rb).length := by
          rcases hdec with ⟨m, x, y, _, _, _, hbm, ham⟩ | ⟨m, x, _, _, hbm, ham⟩
          · have hc1 : (d :: rb).length = (x ::ₘ y ::ₘ m).card := by rw [← Multiset.coe_card, hbm]
            have hc2 : (d_a :: ra).length = ((x - 1) ::ₘ (y - 1) ::ₘ m).card := by
              rw [← Multiset.coe_card, ham]
            simp only [Multiset.card_cons] at hc1 hc2; omega
          · have hc1 : (d :: rb).length = (x ::ₘ m).card := by rw [← Multiset.coe_card, hbm]
            have hc2 : (d_a :: ra).length = ((x - 2) ::ₘ m).card := by
              rw [← Multiset.coe_card, ham]
            simp only [Multiset.card_cons] at hc1 hc2; omega
        cases d_a with
        | zero =>
          -- `a = 0 :: ra`, so `residueAux a = n > n - 1 ≥ residueAux b`
          rw [residueAux_cons_pos hd1, residueAux_cons_zero]
          have hle := residueAux_le_length (SimpleGraph.havelHakimiStep (d :: rb))
          rw [SimpleGraph.havelHakimiStep_length_cons] at hle
          simp only [List.length_cons] at hlen_eq
          omega
        | succ k =>
          let da := k + 1
          change SimpleGraph.residueAux (d :: rb) ≤ SimpleGraph.residueAux (da :: ra)
          have hda1 : 1 ≤ da := by omega
          -- Bound `da ≤ d`
          have hda_le_d : da ≤ d := by
            have hda_in : da ∈ (da :: ra : Multiset ℕ) := by rw [Multiset.mem_coe]; simp
            have hle_b : ∀ z ∈ (d :: rb : Multiset ℕ), z ≤ d := by
              intro z hz
              rw [Multiset.mem_coe] at hz
              rcases List.mem_cons.mp hz with rfl | hmem
              · exact le_rfl
              · exact le_head_of_pairwise_ge hb_pw hmem
            rcases hdec with ⟨m, x, y, _, _, _, hbm, ham⟩ | ⟨m, x, _, _, hbm, ham⟩
            · rw [ham] at hda_in
              rcases Multiset.mem_cons.mp hda_in with h1 | h2
              · have := hle_b x (hbm ▸ Multiset.mem_cons_self x _); omega
              · rcases Multiset.mem_cons.mp h2 with h2' | h3
                · have := hle_b y (hbm ▸ Multiset.mem_cons_of_mem (Multiset.mem_cons_self y _)); omega
                · exact hle_b da (hbm ▸ Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem h3))
            · rw [ham] at hda_in
              rcases Multiset.mem_cons.mp hda_in with h1 | h2
              · have := hle_b x (hbm ▸ Multiset.mem_cons_self x _); omega
              · exact hle_b da (hbm ▸ Multiset.mem_cons_of_mem h2)
          -- Bound `d - 2 ≤ da` and rule out Case B0 (`da + 2 ≤ d`)
          have hda_ge : d - 1 ≤ da := by
            by_contra hlt
            have hda_le_d2 : da + 2 ≤ d := by omega
            have hle_a : ∀ z ∈ (da :: ra : Multiset ℕ), z ≤ da := by
              intro z hz
              rw [Multiset.mem_coe] at hz
              rcases List.mem_cons.mp hz with rfl | hmem
              · exact le_rfl
              · exact le_head_of_pairwise_ge ha_pw hmem
            have hd_in_b : d ∈ (d :: rb : Multiset ℕ) := by rw [Multiset.mem_coe]; simp
            rcases hdec with ⟨m, x, y, _, _, _, hbm, ham⟩ | ⟨m, x, _, hxsafe, hbm, ham⟩
            · rw [hbm] at hd_in_b
              rcases Multiset.mem_cons.mp hd_in_b with rfl | h2
              · have := hle_a (d - 1) (ham ▸ Multiset.mem_cons_self _ _); omega
              · rcases Multiset.mem_cons.mp h2 with rfl | h3
                · have := hle_a (d - 1) (ham ▸ Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _))
                  omega
                · have := hle_a d (ham ▸ Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem h3))
                  omega
            · rw [hbm] at hd_in_b
              rcases Multiset.mem_cons.mp hd_in_b with rfl | h2
              · have hrb_m : (rb : Multiset ℕ) = m := (Multiset.cons_inj_right d).mp hbm
                have hd1_lt : d - 1 < rb.length := by omega
                have hrb_d1_le : rb[d - 1]'hd1_lt ≤ da := by
                  have hmem_m : rb[d - 1]'hd1_lt ∈ m := by
                    rw [← hrb_m, Multiset.mem_coe]; exact List.getElem_mem hd1_lt
                  exact hle_a _ (ham ▸ Multiset.mem_cons_of_mem hmem_m)
                rw [getD_eq_getElem_nat rb hd1_lt] at hxsafe
                omega
              · have := hle_a d (ham ▸ Multiset.mem_cons_of_mem h2)
                omega
          -- Now `da = d` (Case B2) or `da = d - 1` (Case B1)
          rw [residueAux_cons_pos hd1, residueAux_cons_pos hda1,
              havelHakimiStep_cons_eq_phiStep, havelHakimiStep_cons_eq_phiStep]
          have hVb' : IsHHValid (phiStep d rb) := by
            rw [← havelHakimiStep_cons_eq_phiStep]; exact isHHValid_havelHakimiStep hVb
          have hVa' : IsHHValid (phiStep da ra) := by
            rw [← havelHakimiStep_cons_eq_phiStep]; exact isHHValid_havelHakimiStep hVa
          have hlen' : (phiStep d rb).length < n := by
            rw [length_phiStep]; simp at hlen; omega
          rcases Nat.eq_or_lt_of_le hda_le_d with rfl | hda_lt_d
          · -- Case B2: `da = d`
            have hdec_r :
                (∃ (m : Multiset ℕ) (x y : ℕ),
                    1 ≤ y ∧ y ≤ x ∧ y ≤ rb.getD (da - 1) 0 + 1 ∧
                    (rb : Multiset ℕ) = x ::ₘ y ::ₘ m ∧
                    (ra : Multiset ℕ) = (x - 1) ::ₘ (y - 1) ::ₘ m) ∨
                (∃ (m : Multiset ℕ) (x : ℕ),
                    2 ≤ x ∧ x ≤ rb.getD (da - 1) 0 + 1 ∧
                    (rb : Multiset ℕ) = x ::ₘ m ∧
                    (ra : Multiset ℕ) = (x - 2) ::ₘ m) := by
              have hda_in_a : da ∈ (da :: ra : Multiset ℕ) := by rw [Multiset.mem_coe]; simp
              have hle_b : ∀ z ∈ (da :: rb : Multiset ℕ), z ≤ da := by
                intro z hz
                rw [Multiset.mem_coe] at hz
                rcases List.mem_cons.mp hz with rfl | hmem
                · exact le_rfl
                · exact le_head_of_pairwise_ge hb_pw hmem
              rcases hdec with ⟨m, x, y, hy1, hyx, hysafe, hbm, ham⟩ | ⟨m, x, hx2, hxsafe, hbm, ham⟩
              · have hx_le := hle_b x (hbm ▸ Multiset.mem_cons_self x _)
                have hy_le := hle_b y (hbm ▸ Multiset.mem_cons_of_mem (Multiset.mem_cons_self y _))
                have hda_in_m : da ∈ m := by
                  rw [ham] at hda_in_a
                  rcases Multiset.mem_cons.mp hda_in_a with h1 | h2
                  · omega
                  · rcases Multiset.mem_cons.mp h2 with h3 | h4
                    · omega
                    · exact h4
                obtain ⟨m', rfl⟩ := Multiset.exists_cons_of_mem hda_in_m
                refine Or.inl ⟨m', x, y, hy1, hyx, hysafe, ?_, ?_⟩
                · have : da ::ₘ (rb : Multiset ℕ) = da ::ₘ x ::ₘ y ::ₘ m' := by
                    change ((da :: rb : List ℕ) : Multiset ℕ) = _
                    rw [hbm, Multiset.cons_swap y da m', Multiset.cons_swap x da (y ::ₘ m')]
                  exact (Multiset.cons_inj_right da).mp this
                · have : da ::ₘ (ra : Multiset ℕ) = da ::ₘ (x - 1) ::ₘ (y - 1) ::ₘ m' := by
                    change (((k + 1) :: ra : List ℕ) : Multiset ℕ) = _
                    rw [ham, Multiset.cons_swap (y - 1) da m',
                        Multiset.cons_swap (x - 1) da ((y - 1) ::ₘ m')]
                  exact (Multiset.cons_inj_right da).mp this
              · have hx_le := hle_b x (hbm ▸ Multiset.mem_cons_self x _)
                have hda_in_m : da ∈ m := by
                  rw [ham] at hda_in_a
                  rcases Multiset.mem_cons.mp hda_in_a with h1 | h2
                  · omega
                  · exact h2
                obtain ⟨m', rfl⟩ := Multiset.exists_cons_of_mem hda_in_m
                refine Or.inr ⟨m', x, hx2, hxsafe, ?_, ?_⟩
                · have : da ::ₘ (rb : Multiset ℕ) = da ::ₘ x ::ₘ m' := by
                    change ((da :: rb : List ℕ) : Multiset ℕ) = _
                    rw [hbm, Multiset.cons_swap x da m']
                  exact (Multiset.cons_inj_right da).mp this
                · have : da ::ₘ (ra : Multiset ℕ) = da ::ₘ (x - 2) ::ₘ m' := by
                    change (((k + 1) :: ra : List ℕ) : Multiset ℕ) = _
                    rw [ham, Multiset.cons_swap (x - 2) da m']
                  exact (Multiset.cons_inj_right da).mp this
            have hSafe' := safeDoubleDec_caseB2 hb_pw ha_pw hVb hVa hd1 hdec_r
            exact (ih _ hlen').2 _ _ rfl hSafe' hVb' hVa'
          · -- Case B1: `da = d - 1` (so `2 ≤ d`)
            have hda_eq : da = d - 1 := by omega
            have hd2 : 2 ≤ d := by omega
            have hrb_pw : rb.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hb_pw).2
            have hra_pw : ra.Pairwise (· ≥ ·) := (List.pairwise_cons.mp ha_pw).2
            have hd_notin_a : d ∉ (da :: ra : Multiset ℕ) := by
              intro hmem
              rw [Multiset.mem_coe] at hmem
              rcases List.mem_cons.mp hmem with h1 | h2
              · omega
              · have := le_head_of_pairwise_ge ha_pw h2; omega
            have hd_in_b : d ∈ (d :: rb : Multiset ℕ) := by rw [Multiset.mem_coe]; simp
            rcases hdec with ⟨m, x, y, hy1, hyx, hysafe, hbm, ham⟩ | ⟨m, x, hx2, hxsafe, hbm, ham⟩
            · -- Subcase B1b (Distinct)
              have hd_notin_m : d ∉ m := fun hm =>
                hd_notin_a (ham ▸ Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hm))
              have hx_eq_d : x = d := by
                have hle_x : x ≤ d := by
                  have hmem : x ∈ d :: rb := by
                    rw [← Multiset.mem_coe, hbm]; exact Multiset.mem_cons_self x _
                  rcases List.mem_cons.mp hmem with rfl | h
                  · exact le_rfl
                  · exact le_head_of_pairwise_ge hb_pw h
                rw [hbm] at hd_in_b
                rcases Multiset.mem_cons.mp hd_in_b with h1 | h2
                · exact h1.symm
                · rcases Multiset.mem_cons.mp h2 with h3 | h4
                  · omega
                  · exact absurd h4 hd_notin_m
              subst hx_eq_d
              have hrb_coe : (rb : Multiset ℕ) = y ::ₘ m := (Multiset.cons_inj_right x).mp hbm
              have hra_coe : (ra : Multiset ℕ) = (y - 1) ::ₘ m := by
                have h1 : da ::ₘ (ra : Multiset ℕ) = (x - 1) ::ₘ (y - 1) ::ₘ m := ham
                rw [hda_eq] at h1
                exact (Multiset.cons_inj_right (x - 1)).mp h1
              have hpos_ra : ∀ z ∈ ra.take (x - 1), 1 ≤ z := by
                have := ((isHHValid_cons da ra).mp hVa).2.1
                rwa [hda_eq] at this
              rw [hda_eq] at hVa' ⊢
              rcases safeDoubleDec_caseB1b hrb_pw hra_pw hd2 hd_rb hy1 hysafe hpos_ra
                  hrb_coe hra_coe with heq | hEx'
              · rw [heq]
              · exact (ih _ hlen').1 _ _ rfl hEx' hVb' hVa'
            · -- Subcase B1a (Same)
              have hd_notin_m : d ∉ m := fun hm =>
                hd_notin_a (ham ▸ Multiset.mem_cons_of_mem hm)
              have hx_eq_d : x = d := by
                rw [hbm] at hd_in_b
                rcases Multiset.mem_cons.mp hd_in_b with h1 | h2
                · exact h1.symm
                · exact absurd h2 hd_notin_m
              subst hx_eq_d
              have hrb_coe : (rb : Multiset ℕ) = m := (Multiset.cons_inj_right x).mp hbm
              have hra_coe : (x - 1) ::ₘ (ra : Multiset ℕ) = (x - 2) ::ₘ (rb : Multiset ℕ) := by
                rw [hrb_coe, ← hda_eq]; exact ham
              have hrb_le : ∀ z ∈ rb, z ≤ x - 1 := by
                intro z hz
                have hz_m : z ∈ m := by rwa [← hrb_coe, Multiset.mem_coe]
                have hz_a : z ∈ da :: ra := by
                  rw [← Multiset.mem_coe, ham]; exact Multiset.mem_cons_of_mem hz_m
                rcases List.mem_cons.mp hz_a with rfl | h
                · omega
                · have := le_head_of_pairwise_ge ha_pw h; omega
              rw [hda_eq]
              rw [safeDoubleDec_caseB1a hrb_pw hra_pw hd2 hd_rb hrb_le hxsafe hra_coe]

/-! ## 7. Public API Theorems -/

/-- **Option A (Primary Theorem — Elementary Exchange Step Monotonicity):**
Among HH-valid descending degree sequences, moving 1 unit of degree from a smaller-or-equal
positive entry to a larger-or-equal entry (`ExchangeStep s₁ s₂`) cannot lower
`SimpleGraph.residueAux`. -/
theorem residueAux_le_of_exchangeStep {s₁ s₂ : List ℕ}
    (hEx : ExchangeStep s₁ s₂) (h₁ : IsHHValid s₁) (h₂ : IsHHValid s₂) :
    SimpleGraph.residueAux s₁ ≤ SimpleGraph.residueAux s₂ :=
  (residueAux_monotone_aux s₁.length).1 s₁ s₂ rfl hEx h₁ h₂

/-- **Theorem 1(B) (Safe Double-Decrement Monotonicity):**
Applying a safe double-decrement between HH-valid descending degree sequences cannot lower
`SimpleGraph.residueAux`. -/
theorem residueAux_le_of_safeDoubleDec {b a : List ℕ}
    (hSafe : SafeDoubleDec b a) (hb : IsHHValid b) (ha : IsHHValid a) :
    SimpleGraph.residueAux b ≤ SimpleGraph.residueAux a :=
  (residueAux_monotone_aux b.length).2 b a rfl hSafe hb ha

/-- **Transitive HH-Valid Exchange Chain Monotonicity:**
Directly consumes `Relation.ReflTransGen (fun a b => ExchangeStep a b ∧ IsHHValid a ∧ IsHHValid b)`. -/
theorem residueAux_le_of_hhValid_exchangeChain {s₁ s₂ : List ℕ}
    (hChain : Relation.ReflTransGen
      (fun a b => ExchangeStep a b ∧ IsHHValid a ∧ IsHHValid b) s₁ s₂) :
    SimpleGraph.residueAux s₁ ≤ SimpleGraph.residueAux s₂ := by
  induction hChain with
  | refl => exact le_rfl
  | tail _ hstep ih =>
    exact ih.trans (residueAux_le_of_exchangeStep hstep.1 hstep.2.1 hstep.2.2)

/-- **Leaf-Edge Decrement Corollary:**
Decrementing any positive entry `x ≥ 1` and a degree-`1` entry `1` between HH-valid descending
sequences cannot lower `SimpleGraph.residueAux` (Corollary 2(c) at sequence level). -/
theorem residueAux_le_of_leaf_edge_dec {b a : List ℕ}
    (hb_sorted : b.Pairwise (· ≥ ·)) (ha_sorted : a.Pairwise (· ≥ ·))
    (hb : IsHHValid b) (ha : IsHHValid a)
    {m : Multiset ℕ} {x : ℕ} (hx : 1 ≤ x)
    (hbm : (b : Multiset ℕ) = x ::ₘ 1 ::ₘ m)
    (ham : (a : Multiset ℕ) = (x - 1) ::ₘ 0 ::ₘ m) :
    SimpleGraph.residueAux b ≤ SimpleGraph.residueAux a := by
  cases b with
  | nil =>
    have : x ∈ ([] : List ℕ) := by
      rw [← Multiset.mem_coe, hbm]; exact Multiset.mem_cons_self x _
    cases this
  | cons d rb =>
    have hx_mem : x ∈ d :: rb := by
      rw [← Multiset.mem_coe, hbm]; exact Multiset.mem_cons_self x _
    have hx_le : x ≤ d := by
      rcases List.mem_cons.mp hx_mem with rfl | hmem
      · exact le_rfl
      · exact le_head_of_pairwise_ge hb_sorted hmem
    have hd_rb : d ≤ rb.length := ((isHHValid_cons d rb).mp hb).1
    refine residueAux_le_of_safeDoubleDec
      ⟨hb_sorted, ha_sorted, d, rb, rfl, by omega, hd_rb,
        Or.inl ⟨m, x, 1, le_rfl, hx, by omega, hbm, ?_⟩⟩ hb ha
    simpa using ham

/-- **Trailing Zero Identity:**
Appending a `0` to a descending HH-valid sequence increases `SimpleGraph.residueAux` by `1`. -/
theorem residueAux_append_zero {s : List ℕ}
    (hs : s.Pairwise (· ≥ ·)) (hV : IsHHValid s) :
    SimpleGraph.residueAux (s ++ [0]) = SimpleGraph.residueAux s + 1 := by
  induction hn : s.length using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    cases s with
    | nil =>
      simp [residueAux_nil, residueAux_cons_zero]
    | cons d rest =>
      cases d with
      | zero =>
        simp [residueAux_cons_zero]
        omega
      | succ k =>
        obtain ⟨hd_rest, _, hV'⟩ := (isHHValid_cons (k + 1) rest).mp hV
        rw [List.cons_append, residueAux_cons_pos (by omega), residueAux_cons_pos (by omega),
            havelHakimiStep_cons_eq_phiStep, havelHakimiStep_cons_eq_phiStep]
        have hstep_eq : phiStep (k + 1) (rest ++ [0]) = phiStep (k + 1) rest ++ [0] := by
          have hpw_rhs : (phiStep (k + 1) rest ++ [0]).Pairwise (· ≥ ·) := by
            rw [List.pairwise_append]
            exact ⟨pairwise_phiStep (k + 1) rest, List.pairwise_singleton _ _,
              fun x _ y hy => by simp at hy; subst hy; exact Nat.zero_le x⟩
          apply eq_of_coe_eq_of_pairwise (pairwise_phiStep (k + 1) (rest ++ [0])) hpw_rhs
          rw [coe_phiStep, ← Multiset.coe_add, ← Multiset.coe_add, coe_phiStep, ← Multiset.coe_add,
              List.take_append_of_le_length hd_rest, List.drop_append_of_le_length hd_rest,
              ← Multiset.coe_add, add_assoc]
        rw [hstep_eq]
        rw [havelHakimiStep_cons_eq_phiStep] at hV'
        have hlen' : (phiStep (k + 1) rest).length < n := by
          rw [length_phiStep]; simp at hn; omega
        exact ih _ hlen' (pairwise_phiStep (k + 1) rest) hV' rfl

end WOWII61.ResidueSeq
