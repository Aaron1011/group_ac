import Mathlib
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic

variable {f: ℝ → ℝ}

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

-- lemma zero_deriv_implies_poly (a b : ℝ) (n: ℕ) (hf: ∀ (x : ℝ), (x ∈ Set.Icc a b) → (iteratedDerivWithin n f (Set.Icc a b)) x = 0): RestrictsToPoly f a b := by
  -- let temp_f: Set.Icc a b → ℝ := λ z => (iteratedDerivWithin n f (Set.Icc a b)) z
  -- have temp_f_zero: temp_f = λ x => 0 := by
  --   apply funext
  --   intro x
  --   apply hf x
  --   simp


  -- have temp_f_zero_poly: temp_f = λ x: Set.Icc a b => Polynomial.eval ↑x 0 := by
  --   apply funext
  --   intro x
  --   rw [temp_f_zero]
  --   simp [Polynomial.eval_zero]

  -- sorry

lemma zero_first_deriv_implies_poly (a b : ℝ) (hd: DifferentiableOn ℝ f (Set.Icc a b)) (hf: ∀ (x : ℝ), (x ∈ Set.Icc a b) → (derivWithin f (Set.Icc a b) x) = 0): RestrictsToPoly f a b := by
  have smaller:  ∀ (x : ℝ), (x ∈ Set.Ico a b) → (derivWithin f (Set.Icc a b) x) = 0 := by
    refine fun x a ↦ ?_
    apply hf x
    exact Set.mem_Icc_of_Ico a
  have f_eq_constant: ∀ (x: ℝ), x ∈ Set.Icc a b → f x = f a := by apply constant_of_derivWithin_zero hd smaller
  let const_poly: Polynomial ℝ := Polynomial.C (f a)
  have f_eq_const_poly: ∀ (x: ℝ), x ∈ Set.Icc a b → f x = const_poly.eval x := by
    intro x hx
    rw [f_eq_constant x hx]
    rw [Polynomial.eval_C]

  unfold RestrictsToPoly
  exact ⟨const_poly, f_eq_const_poly⟩


lemma zero_deriv_implies_poly (a b : ℝ) (a_lt_b: a < b) (n: ℕ) (hd: ContDiffOn ℝ ⊤ f (Set.Icc a b)) (hf: ∀ (x : ℝ), (x ∈ Set.Icc a b) → (iteratedDerivWithin n f (Set.Icc a b)) x = 0): RestrictsToPoly f a b := by
  have unique_diff: UniqueDiffOn ℝ (Set.Icc a b) := by exact uniqueDiffOn_Icc a_lt_b
  have unique_diff_at : ∀ (x: ℝ), x ∈ (Set.Icc a b) → UniqueDiffWithinAt ℝ (Set.Icc a b) x := unique_diff
  induction n generalizing f with
  | zero =>
    simp only [iteratedDerivWithin_zero] at hf
    unfold RestrictsToPoly
    use 0
    intro y hy
    simp
    apply hf
    exact hy
  | succ k hk =>
    have k_restrict_poly: (∀ x ∈ Set.Icc a b, iteratedDerivWithin k f (Set.Icc a b) x = 0) → RestrictsToPoly f a b := hk hd
    have deriv_succ: ∀ (x: ℝ), x ∈ Set.Icc a b → (iteratedDerivWithin k (derivWithin f (Set.Icc a b)) (Set.Icc a b)) x = 0 := by
      intro x hx
      rw [← iteratedDerivWithin_succ']
      apply hf
      exact hx
      exact unique_diff
      exact hx

    have contdiff_derivative: ContDiffOn ℝ ⊤ (derivWithin f (Set.Icc a b)) (Set.Icc a b) := by
      rw [contDiffOn_top_iff_derivWithin] at hd
      exact hd.2
      exact unique_diff
    have deriv_f_poly: RestrictsToPoly (derivWithin f (Set.Icc a b)) a b := by
      apply hk
      apply contdiff_derivative
      exact deriv_succ

    have f_differentiable: DifferentiableOn ℝ f (Set.Icc a b) := by
      rw [contDiffOn_top_iff_derivWithin] at hd
      exact hd.1
      exact unique_diff

    obtain ⟨p, hp⟩ := deriv_f_poly
    -- The integral of our polynomial, with the constant term set to 0
    let initial_poly_integral: Polynomial ℝ := p.sum fun n a => Polynomial.C (a / (n + 1)) * Polynomial.X ^ (n + 1)
    -- Evaluate it at some arbitrary point (let's pick 'a)
    let initial_poly_at_a: ℝ := Polynomial.eval a initial_poly_integral
    -- Make the polynomial match f at 'a'
    let poly_constant := (f a) - initial_poly_at_a
    -- Now, construct our polynomial integral, satisfying the condition p(a) = f(a)
    let poly_integral := (Polynomial.C poly_constant) + initial_poly_integral
    have deriv_integral : Polynomial.derivative poly_integral = p := by
      simp [poly_integral]
      simp [initial_poly_integral]
      ext n
      rw [Polynomial.coeff_derivative]
      rw [Polynomial.sum]
      simp only [Polynomial.C_mul_X_pow_eq_monomial]
      simp only [← Polynomial.lcoeff_apply, map_sum]
      simp only [Polynomial.lcoeff_apply]
      simp only [Polynomial.coeff_monomial]
      rw [Finset.sum_eq_single (n)]
      . field_simp
      . intro b b_sup b_not_n
        rw [if_neg]
        simp
        simp at b_not_n
        exact b_not_n
      . intro n_not_supp
        rw [Polynomial.mem_support_iff] at n_not_supp
        simp at n_not_supp
        rw [n_not_supp]
        simp

    have deriv_integral_eq_f_deriv: ∀ (x: ℝ), x ∈ Set.Icc a b → derivWithin (fun (y : ℝ) => Polynomial.eval y p) (Set.Icc a b) x = (derivWithin f (Set.Icc a b)) x := by
      sorry

    have eq_at_a: f a = Polynomial.sum a poly_integral := by
      sorry
    have f_eq_deriv_integ ral: ∀(x: ℝ), x ∈ Set.Icc a b → f x = Polynomial.eval x poly_integral := by
      intro x
      apply eq_of_derivWithin_eq f_differentiable
      sorry
      sorry
      apply eq_at_a

    unfold RestrictsToPoly
    exact ⟨poly_integral, f_eq_deriv_integral⟩

-- https://mathoverflow.net/questions/34059/if-f-is-infinitely-differentiable-then-f-coincides-with-a-polynomial
theorem infinite_zero_is_poly (hf: ∀ (x : ℝ), ∃ (n: ℕ), (iteratedDeriv n f) x = 0) (hCInfinity: ContDiff ℝ ⊤ f): RestrictsToPoly f 0 1 := by
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
  have poly_full: poly_intervals = ℝ := by
    sorry

  have unique_diff: ∀ (x c d: ℝ), x ∈ Set.Ioo c d → UniqueDiffWithinAt ℝ (Set.Ioo c d) x := by
    exact fun x c d a ↦ uniqueDiffWithinAt_Ioo a

  let e_n := fun k => { x: ℝ | (iteratedDeriv k f) x = 0 }
  have en_closed: ∀ k: ℕ, IsClosed (e_n k) := by
    intro k
    simp only [e_n]
    --have closed_zero: IsClosed { @Set.Icc _ _ 0 0 } := sorry
    simp [← Set.mem_singleton_iff]
    rw [← Set.preimage]
    apply IsClosed.preimage
    apply ContDiff.continuous_iteratedDeriv k hCInfinity _
    exact OrderTop.le_top _
    exact isClosed_singleton


  --have nonempty_closed_interval: ∀ a b : ℝ, a < b → ((Set.Icc a b) ∩ poly_omega).Nonempty := by
  have nonempty_closed_interval: ∀ a b : ℝ, a < b → ((Set.Icc a b) ∩ poly_omega).Nonempty := by
    intro a b a_lt_b
    have en_intersect_closed: ∀ k: ℕ , IsClosed ((Set.Icc a b ) ∩ (e_n k)) := by
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

    have nonempty: (Set.Icc a b).Nonempty := by
      rw [Set.nonempty_Icc]
      linarith

    have real_nonempty: Nonempty (Set.Icc a b) := by
      rw [Set.nonempty_iff_ne_empty']
      exact Set.nonempty_iff_ne_empty.mp nonempty




    --obtain ⟨interior_index, int_nonempty⟩ := @nonempty_interior_of_iUnion_of_closed (Set.Icc a b) _ _ _ _ _ _ en_intersect_closed en_covers
    -- TODO - we need to apply this to an entire topolgical space. We need [a, b] with the subspace topology
    obtain ⟨interior_index, int_nonempty⟩ := nonempty_interior_of_iUnion_of_closed en_intersect_closed sorry -- en_covers
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

    have cd_subet_omega_ab: Set.Ioo c d ⊆ (Set.Icc a b) ∩ poly_omega := by
      apply Set.subset_inter
      exact cd_subset_ab
      exact cd_subset_omega

    -- rw [Set.nonempty_def]

    --simp at cd_subet_omega_ab
    --have cd_subset_just_omega: Set.Ioo c d ⊆ poly_omega := by
    --  exact cd_subet_omega_ab.1


    --have ioo_c_d_nonempty: (Set.Ioo c d).Nonempty := by
    --  rw [Set.nonempty_Ioo]
    --  linarith

    rw [Set.nonempty_def]
    have cd_nonempty: (Set.Ioo c d).Nonempty := by
      simp
      exact c_lt_d

    rw [Set.nonempty_def] at cd_nonempty
    obtain ⟨elem_cd, h_elem_cd⟩ := cd_nonempty

    have elem_target: elem_cd ∈ (Set.Icc a b) ∩ poly_omega := by
      rw [Set.subset_def] at cd_subet_omega_ab
      apply cd_subet_omega_ab elem_cd h_elem_cd

    exact ⟨elem_cd, elem_target⟩


  let X := poly_omegaᶜ
  have X_closed: IsClosed X := IsOpen.isClosed_compl poly_open
  have X_empty: X = ∅ := by
    have x_accum: ∀ x, x ∈ X → AccPt x (Filter.principal X) := by
      by_contra!
      obtain ⟨x, ⟨x_in, x_not_acc⟩⟩ := this
      rw [accPt_iff_nhds] at x_not_acc
      simp at x_not_acc
      obtain ⟨u, hu⟩ := x_not_acc
      obtain ⟨g, h, x_in_gh, gh_in_u⟩ := mem_nhds_iff_exists_Ioo_subset.mp hu.1

      have g_lt_x: g < x := by
        simp [Set.mem_Ioo] at x_in_gh
        exact x_in_gh.1

      have x_lt_h: x < h := by
        simp [Set.mem_Ioo] at x_in_gh
        exact x_in_gh.2

      have _: ∀ y: ℝ, y ∈ (Set.Ioo g x) → y ∈ poly_omega := by
        sorry

      have _: ∀ y: ℝ, y ∈ (Set.Ioo x h) → y ∈ poly_omega := by
        sorry

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

    have n_succ_deriv_zero: ∀ (x: ℝ), x ∈ Set.Ioo c d → (iteratedDerivWithin (n_x_int + 1) f (Set.Ioo c d)) x = 0 := by
      intro x hx
      have unique_diff_at : UniqueDiffWithinAt ℝ (Set.Ioo c d) x := by
        apply unique_diff x
        assumption
      rw [iteratedDerivWithin_succ unique_diff_at]

      have deriv_within: HasDerivWithinAt (iteratedDerivWithin n_x_int f (Set.Ioo c d)) 0 (Set.Ioo c d) x := by
        --rw [hasDerivWithinAt_iff_tendsto_slope]
        sorry
      apply HasDerivWithinAt.derivWithin deriv_within
      sorry

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

    have cd_nonempty: (Set.Ioo c d).Nonempty := by
      simp
      exact c_lt_d

    obtain ⟨q, hq⟩ := Set.nonempty_def.mp cd_nonempty
    have _: q ∈ X := by
      apply cd_subset_x
      exact hq
    have _: q ∈ poly_omega := by
      apply cd_subset_omega
      exact hq

    contradiction

  have poly_comp_empty: poly_omegaᶜ = ∅ := by
    apply X_empty
  have poly_full: poly_omega = (Set.univ) := by
    exact Set.compl_empty_iff.mp X_empty



  sorry

    --apply is_closed_iff_forall_subset_is_closed.mp (en_closed k)
    --apply Set.Icc_subset_Icc
