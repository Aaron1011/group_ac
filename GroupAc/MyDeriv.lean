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
theorem infinite_zero_is_poly (hf: ∀ (x : ℝ), ∃ (n: ℕ), (iteratedFDeriv ℝ n f) x = 0) (hCInfinity: ContDiffOn ℝ ⊤ f {x: ℝ | True}): RestrictsToPoly f 0 1 := by
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
    have x_accum: ∀ x, x ∈ X → AccPt x (Filter.principal X) := by
      by_contra!
      obtain ⟨x, ⟨x_in, x_not_acc⟩⟩ := this
      rw [accPt_iff_nhds] at x_not_acc
      simp at x_not_acc
      obtain ⟨u, hu⟩ := x_not_acc
      rw [nhds_def] at hu

      have g : ℝ := by sorry
      have g_lt_x: g < x := by sorry
      have h : ℝ := by sorry
      have x_lt_h: x < h := by sorry

      -- TODO - get this intervals from the fact that x is an isolated point
      have _: (Set.Ioo g x) ⊆ poly_omega := by sorry
      have _: (Set.Ioo x h) ⊆ poly_omega := by sorry

      have is_first_poly: RestrictsToPoly f g x := by sorry
      have is_second_poly: RestrictsToPoly f x h := by sorry

      obtain ⟨first_poly, h_first_poly⟩ := is_first_poly
      obtain ⟨second_poly, h_second_poly⟩ := is_second_poly

      let n := max first_poly.natDegree second_poly.natDegree
      have zero_on_new: ∀ (y: ℝ), y ∈ (Set.Ioo g x ∪ Set.Ioo x h) → (iteratedDerivWithin n f (Set.Ioo g x ∪ Set.Ioo x h)) y = 0 := by
        have degree_zero: ((⇑Polynomial.derivative)^[n] first_poly).natDegree ≤ first_poly.natDegree - n := by
          apply Polynomial.natDegree_iterate_derivative first_poly n
        simp at degree_zero
        have first_le_n : first_poly.natDegree ≤ n := by exact Nat.le_max_left first_poly.natDegree second_poly.natDegree
        have real_degree_zero: ((⇑Polynomial.derivative)^[n] first_poly).natDegree ≤ 0 := by sorry

        have first_zero: ((⇑Polynomial.derivative)^[n] first_poly) = 0 := by sorry
        have second_zero: ((⇑Polynomial.derivative)^[n] second_poly) = 0 := by sorry

        have f_deriv_zero: ∀ (y: ℝ), y ∈ (Set.Ioo g x ∪ Set.Ioo x h) → (iteratedDerivWithin n f (Set.Ioo g x ∪ Set.Ioo x h)) y = 0 := by
          sorry

        -- Use continuity here
        have f_deriv_at_x: (iteratedDerivWithin n f (Set.Ioo g h)) x = 0 := sorry
        -- f^(n) is zero on (g, x) and (x, h), and x, so it's zero on (g, h)
        have f_zero_full: ∀ (y: ℝ), y ∈ (Set.Ioo g h) → (iteratedDerivWithin n f (Set.Ioo g h)) y = 0 := sorry
        sorry

      have f_poly_full: RestrictsToPoly f g h := by sorry
      have gh_in_omega: Set.Ioo g h ⊆ poly_omega := by
        simp [poly_omega]
        rw [Set.subset_def]
        intro y hy
        simp only [Set.mem_sUnion]
        use Set.Ioo g h
        simp
        constructor
        exact ⟨g, h, rfl, f_poly_full⟩
        exact hy

      have x_in_gh: x ∈ Set.Ioo g h := by
        simp
        exact ⟨g_lt_x, x_lt_h⟩

      have x_in_omega: x ∈ poly_omega := by
        apply gh_in_omega
        exact x_in_gh
      contradiction

    have x_intersect_closed: ∀ k: ℕ , IsClosed (X ∩ (e_n k)) := by
      intro k
      apply IsClosed.inter
      exact X_closed
      apply en_closed k

    have x_union_en: X = Set.iUnion fun j => X ∩ (e_n j) := by
      ext p
      obtain ⟨n, hn⟩ := hf p
      have p_in_en: p ∈ (e_n n) := by
        simp only [e_n]
        simp
        exact hn

      constructor
      intro p_in_x
      have p_in_intersect: p ∈ X ∩ (e_n n):= by
        apply Set.mem_inter
        exact p_in_x
        exact p_in_en

      simp only [Set.mem_iUnion]
      exact ⟨n, p_in_intersect⟩
      -- second case
      intro p_in_union
      simp only [Set.mem_iUnion] at p_in_union
      obtain ⟨_, p_in_intersect⟩ := p_in_union
      exact p_in_intersect.1

    have en_cov_univ_set_x: (Set.iUnion fun j => X ∩ (e_n j)) = Set.univ := by
      sorry

    by_contra!

    rw [eq_comm] at x_union_en
    obtain ⟨n_x_int, x_int_nonempty⟩ := nonempty_interior_of_iUnion_of_closed x_intersect_closed en_cov_univ_set_x
    let x_int := (interior (X ∩ e_n n_x_int))
    have x_int_open: IsOpen x_int := by apply isOpen_interior
    obtain ⟨c, d, c_lt_d, cd_int⟩ := IsOpen.exists_Ioo_subset x_int_open x_int_nonempty
    have x_zero_on_cd: ∀ (x: ℝ), x ∈ Set.Ioo c d → (iteratedDerivWithin n_x_int f (Set.Ioo c d)) x = 0 :=
      by sorry

    have unique_diff: ∀ (x: ℝ), x ∈ Set.Ioo c d → UniqueDiffWithinAt ℝ (Set.Ioo c d) x := by
      apply uniqueDiffWithinAt_Ioo

    have n_succ_deriv_zero: ∀ (x: ℝ), x ∈ Set.Ioo c d → (iteratedDerivWithin (n_x_int + 1) f (Set.Ioo c d)) x = 0 := by
      intro x hx
      have unique_diff_at : UniqueDiffWithinAt ℝ (Set.Ioo c d) x := by
        apply unique_diff x hx
      rw [iteratedDerivWithin_succ unique_diff_at]

      have deriv_within: HasDerivWithinAt (iteratedDerivWithin n_x_int f (Set.Ioo c d)) 0 (Set.Ioo c d) x := by
        --rw [hasDerivWithinAt_iff_tendsto_slope]
        sorry
      exact HasDerivWithinAt.derivWithin deriv_within (unique_diff x hx)

    have forall_deriv_zero: ∀ (m: ℕ), m ≥ n_x_int →  ∀ (x: ℝ), x ∈ X ∩ Set.Ioo c d → (iteratedDerivWithin m f (Set.Ioo c d)) x = 0 := by
      intro m hm
      induction m with
      | zero => sorry
      | succ a ha => sorry

    have deriv_zero_on_cd_omega: ∀ (x : ℝ), x ∈ Set.Ioo c d → (iteratedDerivWithin n_x_int f (Set.Ioo c d)) x = 0 := by
      sorry

    have poly_on_cd: RestrictsToPoly f c d := by apply zero_deriv_implies_poly c d n_x_int deriv_zero_on_cd_omega
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
    have int_subset_x_int: x_int ⊆ X ∩ e_n n_x_int := interior_subset
    have int_subset_x: x_int ⊆ X := by sorry
    have cd_subset_x: Set.Ioo c d ⊆ X := by sorry
    simp [X] at cd_subset_x

    -- TODO - obtain this from our subsets above
    have q: ℝ := sorry
    have _: q ∈ X := by sorry
    have _: q ∉ X := by sorry

    contradiction

  have poly_comp_empty: poly_omegaᶜ = ∅ := by
    apply X_empty
  have poly_full: poly_omega = (Set.univ) := by
    exact Set.compl_empty_iff.mp X_empty

  sorry

    --apply is_closed_iff_forall_subset_is_closed.mp (en_closed k)
    --apply Set.Icc_subset_Icc
