import Mathlib
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic

variable {f}

def RestrictsToPoly (f: ℝ → ℝ) (a b: ℝ) :=
  ∃ (p: Polynomial ℝ), ∀ (y: ℝ), y ∈ Set.Icc a b → f y = p.eval y

lemma poly_n_induct (n k: ℕ) (p: Polynomial ℝ) (hp1: ((Polynomial.derivative)^[n] p).degree < k) : (p.degree < n + k) := by
  induction n generalizing k with
  | zero =>
    simp at hp1
    simp
    exact hp1
  | succ a ha =>
    rw [Function.iterate_succ'] at hp1
    simp at hp1

    have partial_lt: (Polynomial.derivative ((Polynomial.derivative)^[a] p)).degree ≤ ((⇑Polynomial.derivative)^[a] p).degree := by
      apply Polynomial.degree_derivative_le

    have h2: (Polynomial.derivative ((⇑Polynomial.derivative)^[a] p)).degree < k := by
      sorry
      --apply lt_of_le_of_lt' partial_lt (ha 1)
    sorry

lemma zero_deriv_implies_poly (a b : ℝ) (n: ℕ) (hf: ∀ (x : ℝ), (x ∈ Set.Ioo a b) → (iteratedDerivWithin n f (Set.Ioo a b)) x = 0): RestrictsToPoly f a b := by
  let temp_f: Set.Ioo a b → ℝ := λ z => (iteratedDerivWithin n f (Set.Ioo a b)) z
  have temp_f_zero: temp_f = λ x => 0 := by
    simp only [temp_f]
    apply funext
    intro x
    apply hf x
    simp

  have temp_f_zero_poly: temp_f = λ x: Set.Ioo a b => Polynomial.eval ↑x 0 := by
    apply funext
    intro x
    rw [temp_f_zero]
    simp [Polynomial.eval_zero]



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

    have en_cov_univ_set: (Set.iUnion fun j => (Set.Icc a b) ∩ (e_n j)) = Set.univ := by
      sorry

    obtain ⟨interior_index, int_nonempty⟩ := nonempty_interior_of_iUnion_of_closed en_intersect_closed en_cov_univ_set
    have int_open: IsOpen (interior (Set.Icc a b ∩ e_n interior_index)) := by apply isOpen_interior
    obtain ⟨c, d, c_lt_d, cd_int⟩ := IsOpen.exists_Ioo_subset int_open int_nonempty
    have zero_on_cd: ∀ (x: ℝ), x ∈ (Set.Ioo c d) → (iteratedDerivWithin interior_index f (Set.Ioo c d)) x = 0 := by sorry
    have poly_on_cd: RestrictsToPoly f c d := by apply zero_deriv_implies_poly c d interior_index zero_on_cd
    have cd_subset_omega: Set.Ioo c d ⊆ poly_omega := by
      simp [poly_omega]
      rw [Set.subset_def]
      intro x hx
      simp only [Set.mem_sUnion]
      use Set.Ioo c d
      simp
      constructor
      exact ⟨c, d, rfl, poly_on_cd⟩
      exact hx

    have cd_subset_ab: Set.Ioo c d ⊆ Set.Icc a b := by
      simp at cd_int
      have cd_subset: (Set.Ioo c d) ⊆ Set.Ioo a b := by exact cd_int.1
      have io_lt: Set.Ioo a b ⊆ Set.Icc a b := Set.Ioo_subset_Icc_self
      apply subset_trans cd_subset io_lt

    have cd_subet_omega_ab: Set.Ioo c d ⊆ poly_omega ∩ Set.Icc a b := by
      apply Set.subset_inter
      exact cd_subset_omega
      exact cd_subset_ab


    let X := poly_omegaᶜ
    have X_closed: IsClosed X := IsOpen.isClosed_compl poly_open
    have X_empty: X = ∅ := by
      by_contra!
      sorry
    --apply is_closed_iff_forall_subset_is_closed.mp (en_closed k)
    --apply Set.Icc_subset_Icc
