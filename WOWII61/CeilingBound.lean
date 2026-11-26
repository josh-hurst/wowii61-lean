module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

public section

namespace WOWII61

/-- Convert the integer forest bound to the real-valued statement used upstream. -/
theorem realCeilingBound (d r f : ℕ) (h : r + (d + 2) / 3 ≤ f) :
    (r : ℝ) + ⌈(d : ℝ) / 3⌉ ≤ (f : ℝ) := by
  have hmul : d ≤ ((d + 2) / 3) * 3 := by omega
  have hdiv : (d : ℝ) / 3 ≤ ((((d + 2) / 3 : ℕ) : ℤ) : ℝ) := by
    apply (div_le_iff₀ (by exact_mod_cast (show 0 < (3 : ℕ) by decide) : (0 : ℝ) < 3)).2
    exact_mod_cast hmul
  have hceil : ⌈(d : ℝ) / 3⌉ ≤ (((d + 2) / 3 : ℕ) : ℤ) := Int.ceil_le.mpr hdiv
  have hcast : ((⌈(d : ℝ) / 3⌉ : ℤ) : ℝ) ≤ (((d + 2) / 3 : ℕ) : ℝ) := by
    simpa only [Int.cast_natCast] using (Int.cast_le (R := ℝ)).mpr hceil
  calc
    _ ≤ (r : ℝ) + (((d + 2) / 3 : ℕ) : ℝ) := add_le_add le_rfl hcast
    _ ≤ _ := by exact_mod_cast h

end WOWII61
