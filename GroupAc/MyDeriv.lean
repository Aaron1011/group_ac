import Mathlib

variable {f}

theorem infinite_zero_is_poly (hf: ∀ (x : ℝ), x ∈ (Set.Icc 0 1) → ∃ (n: ℕ), (iteratedFDerivWithin n f (Set.Icc 0 1)) x) : IsPoly f :=
  sorry
