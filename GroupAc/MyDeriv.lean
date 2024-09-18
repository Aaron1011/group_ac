import Mathlib
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic

variable {f}

def RestrictsToPoly (f: ℝ → ℝ) (a b: ℝ) :=
  ∃ (p: Polynomial ℝ), ∀ (y: ℝ), y ∈ Set.Icc a b → f y = p.eval y

-- https://mathoverflow.net/questions/34059/if-f-is-infinitely-differentiable-then-f-coincides-with-a-polynomial
theorem infinite_zero_is_poly (hf: ∀ (x : ℝ), ∃ (n: ℕ), (iteratedFDeriv ℝ n f) x = 0): RestrictsToPoly f 0 1 := by
  -- let real_powset := 𝒫 { z: ℝ | True }
  let poly_omega := Set.sUnion { i | ∃ (a b : ℝ ), i = Set.Ioo a b ∧ RestrictsToPoly f a b }
  have poly_open: IsOpen poly_omega := by
    apply isOpen_sUnion
    intro t ht
    simp at ht
    obtain ⟨a, b, h, h'⟩ := ht
    rw [h]
    apply isOpen_Ioo

  obtain ⟨poly_intervals, hIntervals⟩ := TopologicalSpace.IsTopologicalBasis.open_eq_sUnion Real.isTopologicalBasis_Ioo_rat poly_open
  have _: poly_intervals.Countable := by
    sorry

  have poly_full: poly_intervals = ℝ := by
    sorry

  let e_n := fun k => { x: ℝ | (iteratedFDeriv ℝ k f) x = 0 }
  have en_closed: ∀ k: ℕ, IsClosed (e_n k) := by
    intro k
    simp only [e_n]
    sorry

  have nonempty_closed_interval: ∀ a b : ℝ, ((Set.Icc a b) ∩ poly_omega).Nonempty := by
    intro a b
    have en_intersect_closed: ∀ k: ℕ , IsClosed ((Set.Icc a b) ∩ (e_n k)) := by
      intro k
      apply IsClosed.inter
      apply isClosed_Icc
      apply en_closed k

    have en_covers: (Set.Icc a b) = Set.iUnion fun j => ((e_n j) ∩ Set.Icc a b) := by
      ext p
      obtain ⟨n, hn⟩ := hf p
      have p_in_en: p ∈ (e_n n) := by
        simp only [e_n]
        simp
        exact hn


      --have p_implies_in_en: fun h_new => (p ∈ (e_n n) (e_n n) ∩ Set.Icc a b) := by
      --  simp only [e_n]
      --  apply And.intro p_in_en h_new

      constructor
      -- first case
      intro p_in_interval
      have p_in_intersect: p ∈ (e_n n) ∩ Set.Icc a b := by
        apply Set.mem_inter
        exact p_in_en
        exact p_in_interval

      simp only [Set.mem_iUnion]
      exact ⟨n, p_in_intersect⟩
      -- second case

      simp



    --apply is_closed_iff_forall_subset_is_closed.mp (en_closed k)
    --apply Set.Icc_subset_Icc
