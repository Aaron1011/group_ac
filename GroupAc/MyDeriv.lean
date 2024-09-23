import Mathlib
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.Basic

open Topology
open Filter

variable {f: ℝ → ℝ}

def RestrictsToPoly (f: ℝ → ℝ) (a b: ℝ) :=
  ∃ (p: Polynomial ℝ), ∀ (y: ℝ), y ∈ Set.Ioo a b → f y = p.eval y

-- variable {f' g : ℝ → ℝ }

-- open Metric Set Asymptotics ContinuousLinearMap Filter
-- open scoped Topology NNReal

-- theorem eq_of_has_deriv_right_eq_open (derivf : ∀ x ∈ Set.Ioo a b, HasDerivWithinAt f (f' x) (Set.Ici x) x)
--     (derivg : ∀ x ∈ Set.Ioo a b, HasDerivWithinAt g (f' x) (Set.Ici x) x) (fcont : ContinuousOn f (Set.Ioo a b))
--     (gcont : ContinuousOn g (Set.Ioo a b)) (hi : ∃ p ∈ (Set.Ioo) a b, f p = g p) : ∀ y ∈ Set.Ioo a b, f y = g y := by
--   simp only [← @sub_eq_zero _ _ (f _)] at hi ⊢
--   obtain ⟨p, hp⟩ := hi
--   exact hp.2 ▸ constant_of_has_deriv_right_zero (fcont.sub gcont) fun y hy => by
--     simpa only [sub_self] using (derivf y hy).sub (derivg y hy)

-- theorem eq_of_derivWithin_eq_open (a b: ℝ) (fdiff : DifferentiableOn ℝ f (Set.Ioo a b))
--     (gdiff : DifferentiableOn ℝ g (Set.Ioo a b))
--     (hderiv : Set.EqOn (derivWithin f (Set.Ioo a b)) (derivWithin g (Set.Ioo a b)) (Set.Ioo a b)) (hi : ∃ p ∈ Set.Icc a b, f p = g p) :
--     ∀ y ∈ Set.Ioo a b, f y = g y := by
--   have A : ∀ y ∈ Set.Ioo a b, HasDerivWithinAt f (derivWithin f (Set.Ioo a b) y) (Set.Ici y) y := fun y hy =>
--     (fdiff y hy).hasDerivWithinAt.mono_of_mem (Ioo_mem_nhdsWithin_Ici hy)
--   have B : ∀ y ∈ Set.Ioo a b, HasDerivWithinAt g (derivWithin g (Set.Ioo a b) y) (Set.Ici y) y := fun y hy =>
--     (gdiff y hy).hasDerivWithinAt.mono_of_mem (Ioo_mem_nhdsWithin_Ici hy)
--   exact
--     eq_of_has_deriv_right_eq A (fun y hy => (hderiv hy).symm ▸ B y hy) fdiff.continuousOn
--       gdiff.continuousOn hi

-- end

-- f = λ y => p.eval y

lemma const_ioo_implies_endpoint_left (a b k: ℝ) (hlt: a < b) (hc: ContinuousOn f (Set.Icc a b)) (hConst: ∀ x, x ∈ (Set.Ioo a b) → f x = k) : f a = k := by
  have tendsto_left: Tendsto f (𝓝[Set.Icc a b] a) (𝓝 (f a)) := by
    apply ContinuousWithinAt.tendsto (ContinuousOn.continuousWithinAt _ _)
    apply hc
    simp
    exact le_of_lt hlt

  have ab_subset: Set.Ioo a b ⊆ Set.Icc a b := by
    apply Set.Ioo_subset_Icc_self

  have tendsto_shrink: Tendsto f (𝓝[Set.Ioo a b] a) (𝓝 (f a)) := by
    apply tendsto_nhdsWithin_mono_left ab_subset tendsto_left

  have k_in_self: ∀ n, n ∈ (𝓝 (k)) → k ∈ n := by
    exact fun n a ↦ mem_of_mem_nhds a

  have h2: Tendsto f (𝓝[Set.Ioo a b] a) (𝓝 (k)) := by
    rw [Filter.tendsto_def]
    intro s hs
    simp [mem_nhdsWithin]
    use Set.Ioo (a - 1) b
    refine ⟨isOpen_Ioo, ?_, ?_⟩
    simp
    exact hlt
    rw [Set.subset_def]
    intro h ⟨_, hx⟩
    simp
    rw [hConst]
    exact k_in_self s hs
    exact hx

  have ne_bot: (𝓝[Set.Ioo a b] a).NeBot := by
    apply IsGLB.nhdsWithin_neBot
    apply isGLB_Ioo
    exact hlt
    simp [Set.nonempty_Ioo]
    exact hlt

  have h_left_eq: f a = k := by
    apply tendsto_nhds_unique tendsto_shrink h2

  exact h_left_eq

lemma const_ioo_implies_endpoint_right (a b k: ℝ) (hlt: a < b) (hc: ContinuousOn f (Set.Icc a b)) (hConst: ∀ x, x ∈ (Set.Ioo a b) → f x = k) : f b = k := by
  let f_swap := f ∘ (λ x: ℝ => (b + (a - x)))
  have f_swap_const: ∀ x, x ∈ (Set.Ioo a b) → f_swap x = k := by
    intro x hx
    simp [f_swap]
    apply hConst
    simp
    simp at hx
    refine ⟨?_, ?_⟩
    linarith
    linarith

  have f_swap_left: f_swap a = k := by
    apply const_ioo_implies_endpoint_left a b k hlt _ f_swap_const
    simp [f_swap]
    apply ContinuousOn.comp hc _
    rw [Set.MapsTo]
    intro x hx
    simp at hx
    simp
    refine ⟨?_, ?_⟩
    linarith
    linarith
    refine ContinuousOn.add ?hf ?hg
    exact continuousOn_const
    apply Continuous.continuousOn (continuous_sub_left a)


  simp [f_swap] at f_swap_left
  exact f_swap_left

lemma zero_deriv_implies_poly (a b : ℝ) (n: ℕ) (a_lt_b: a < b) (hd: ContDiffOn ℝ ⊤ f (Set.Icc a b)) (hf: ∀ (x : ℝ), (x ∈ Set.Ioo a b) → (iteratedDerivWithin n f (Set.Icc a b)) x = 0): RestrictsToPoly f a b := by
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
    have k_restrict_poly: (∀ x ∈ Set.Ioo a b, iteratedDerivWithin k f (Set.Icc a b) x = 0) → RestrictsToPoly f a b := hk hd
    have deriv_succ: ∀ (x: ℝ), x ∈ Set.Ioo a b → (iteratedDerivWithin k (derivWithin f (Set.Icc a b)) (Set.Icc a b)) x = 0 := by
      intro x hx
      rw [← iteratedDerivWithin_succ']
      apply hf
      exact hx
      exact unique_diff
      exact Set.mem_Icc_of_Ioo hx

    --have contdiff_derivative: ContDiff ℝ ⊤ (iteratedDerivWithin k f (Set.Icc a b)) := by
    --  apply ContDiff.of_succ

    have contdiffon_derivative: ContDiffOn ℝ ⊤ (derivWithin f (Set.Icc a b)) (Set.Icc a b) := by
      rw [contDiffOn_top_iff_derivWithin] at hd
      exact hd.2
      exact unique_diff

    have deriv_continuous: ContinuousOn (derivWithin f (Set.Icc a b)) (Set.Icc a b) := by
      apply ContDiffOn.continuousOn contdiffon_derivative

    have deriv_f_poly: RestrictsToPoly (derivWithin f (Set.Icc a b)) a b := by
      apply hk
      apply contdiffon_derivative
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
      . intro b _ b_not_n
        rw [if_neg]
        simp
        simp at b_not_n
        exact b_not_n
      . intro n_not_supp
        rw [Polynomial.mem_support_iff] at n_not_supp
        simp at n_not_supp
        rw [n_not_supp]
        simp


    have deriv_integral_eq_poly_deeriv: ∀ (x: ℝ), x ∈ Set.Icc a b → derivWithin (fun (y : ℝ) => Polynomial.eval y poly_integral) (Set.Icc a b) x = Polynomial.eval x (Polynomial.derivative poly_integral) := by
      intro x hx
      apply Polynomial.derivWithin poly_integral
      exact unique_diff_at x hx

    have eq_at_a: f a = Polynomial.eval a poly_integral := by
      simp [poly_integral, initial_poly_integral, poly_constant]

    have deriv_minus_is_const: ∀y, y ∈ Set.Ioo a b → (derivWithin f (Set.Icc a b) y) - p.eval y = 0 := by
      intro y hy
      rw [hp]
      simp
      exact hy

    have deriv_minus_eq_zero_at_a: (derivWithin f (Set.Icc a b)) a - p.eval a = 0 := by
      apply @const_ioo_implies_endpoint_left (λ y => (derivWithin f (Set.Icc a b) y) - p.eval y)
      apply a_lt_b
      apply ContinuousOn.sub
      apply deriv_continuous
      exact Polynomial.continuousOn_aeval p
      apply deriv_minus_is_const

    have deriv_eq_at_a: (derivWithin f (Set.Icc a b)) a = Polynomial.eval a p := by
      exact eq_of_sub_eq_zero deriv_minus_eq_zero_at_a

    have f_eq_deriv_integral: ∀(x: ℝ), x ∈ Set.Ioo a b → f x = Polynomial.eval x poly_integral := by
      intro x hx
      have eq_on_icc: ∀ y ∈ Set.Icc a b, f y = poly_integral.eval y:= by
        apply eq_of_derivWithin_eq f_differentiable
        apply Polynomial.differentiableOn
        rw [Set.EqOn]
        intro y hy
        rw [deriv_integral_eq_poly_deeriv]
        rw [deriv_integral]
        by_cases y_eq_a: y = a
        . rw [y_eq_a]
          apply deriv_eq_at_a
        . apply hp
          apply Set.eq_left_or_mem_Ioo_of_mem_Ico at hy
          simp [y_eq_a] at hy
          simp
          exact hy

        apply Set.mem_Icc_of_Ico
        exact hy
        apply eq_at_a
      apply eq_on_icc
      apply Set.mem_Icc_of_Ioo
      exact hx

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

    have int_subset_a_b: interior (Set.Icc a b ∩ e_n interior_index) ⊆ Set.Icc a b := by
      rw [Set.subset_def]
      intro y hy
      simp only [mem_interior] at hy
      simp only [Set.subset_def] at hy
      obtain ⟨t, ht, h_other_t, y_in_t⟩ := hy
      specialize ht y y_in_t
      exact ht.1


    have cont_diff_on: ContDiffOn ℝ ⊤ f (Set.Icc c d) := ContDiff.contDiffOn hCInfinity
    have zero_on_cd: ∀ (x: ℝ), x ∈ (Set.Ioo c d) → (iteratedDerivWithin interior_index f (Set.Ioo c d)) x = 0 := by
      intro x hx
      simp at cd_int
      dsimp [e_n] at cd_int
      simp only [Set.subset_def] at cd_int
      simp only [mem_interior] at cd_int
      simp only [Set.subset_def] at cd_int
      simp only [Set.mem_setOf_eq] at cd_int
      obtain ⟨t, ht⟩ := cd_int
      specialize ht x hx
      simp only [Set.mem_def] at ht
      obtain ⟨other_t, h_other_t⟩ := ht
      have iter_x: (∀ (x : ℝ), other_t x → iteratedDeriv interior_index f x = 0) := h_other_t.1
      specialize iter_x x h_other_t.2.2
      rw [iteratedDerivWithin]
      rw [iteratedDeriv] at iter_x
      have derives_eq: Set.EqOn (iteratedFDerivWithin ℝ interior_index f (Set.Ioo c d)) (iteratedFDeriv ℝ interior_index f) (Set.Ioo c d) :=
        by apply iteratedFDerivWithin_of_isOpen interior_index (isOpen_Ioo)
      rw [Set.EqOn] at derives_eq
      simp

      have zero_on_open: (iteratedFDerivWithin ℝ interior_index f (Set.Ioo c d)) x (fun x ↦ 1) = 0 := by
        simp only [derives_eq]
        specialize derives_eq hx
        rw [derives_eq]
        exact iter_x

      apply zero_on_open

    have poly_on_cd: RestrictsToPoly f c d := by apply zero_deriv_implies_poly c d interior_index c_lt_d cont_diff_on sorry -- zero_on_cd
    have cd_subset_omega: Set.Ioo c d ⊆ poly_omega := by
      simp [poly_omega]
      rw [Set.subset_def]
      intro x hx
      simp only [Set.mem_sUnion]
      use Set.Ioo c d
      simp only [Set.mem_setOf_eq]
      constructor
      dsimp [RestrictsToPoly]
      obtain ⟨p, hp⟩ := poly_on_cd
      use c
      use d
      simp only [and_imp, true_and]
      use p
      simp at cd_int
      exact hx

    have cd_subet_omega_ab: Set.Icc c d ⊆ (Set.Icc a b) ∩ poly_omega := by
      apply Set.subset_inter
      apply subset_trans cd_int int_subset_a_b
      apply cd_subset_omega

    -- rw [Set.nonempty_def]

    --simp at cd_subet_omega_ab
    --have cd_subset_just_omega: Set.Ioo c d ⊆ poly_omega := by
    --  exact cd_subet_omega_ab.1


    --have ioo_c_d_nonempty: (Set.Ioo c d).Nonempty := by
    --  rw [Set.nonempty_Ioo]
    --  linarith

    rw [Set.nonempty_def]
    have cd_nonempty: (Set.Icc c d).Nonempty := by
      simp
      apply le_of_lt c_lt_d

    rw [Set.nonempty_def] at cd_nonempty
    obtain ⟨elem_cd, h_elem_cd⟩ := cd_nonempty

    have elem_target: elem_cd ∈ (Set.Icc a b) ∩ poly_omega := by
      rw [Set.subset_def] at cd_subet_omega_ab
      apply cd_subet_omega_ab elem_cd _
      exact h_elem_cd


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
    have x_zero_on_cd: ∀ (x: ℝ), x ∈ Set.Ioo c d → (iteratedDerivWithin n_x_int f (Set.Ioo c d)) x = 0 := by
      dsimp [x_int] at cd_int
      dsimp [interior, e_n] at cd_int
      rw [Set.subset_def] at cd_int
      intro x hx
      specialize cd_int x hx
      simp only [Set.mem_sUnion] at cd_int
      obtain ⟨t, ht, hxt⟩ := cd_int
      rw [Set.mem_setOf_eq] at ht
      have t_subset: t ⊆ X ∩ {x | iteratedDeriv n_x_int f x = 0} := ht.2
      apply Set.mem_of_subset_of_mem t_subset at hxt
      apply Set.mem_of_mem_inter_right at hxt
      rw [Set.mem_setOf_eq] at hxt
      have eq_on: Set.EqOn (iteratedFDerivWithin ℝ n_x_int f (Set.Ioo c d)) (iteratedFDeriv ℝ n_x_int f) (Set.Ioo c d) :=
        by apply iteratedFDerivWithin_of_isOpen n_x_int isOpen_Ioo
      dsimp [Set.EqOn] at eq_on
      specialize eq_on hx
      dsimp [iteratedDeriv] at hxt
      dsimp [iteratedDerivWithin]
      rw [eq_on]
      apply hxt

    have n_succ_deriv_zero: ∀ (x: ℝ), x ∈ Set.Ioo c d → (iteratedDerivWithin (n_x_int + 1) f (Set.Ioo c d)) x = 0 := by
      intro x hx
      have unique_diff_at : UniqueDiffWithinAt ℝ (Set.Ioo c d) x := by
        apply unique_diff x
        assumption
      rw [iteratedDerivWithin_succ unique_diff_at]
      have deriv_x_zero: (iteratedDerivWithin n_x_int f (Set.Ioo c d)) x = 0 := by
        apply x_zero_on_cd x hx

      have cont_diff_within_at: ContDiffWithinAt ℝ ⊤ (iteratedDerivWithin n_x_int f (Set.Ioo c d)) (Set.Ioo c d) c := by
        --apply ContDiff.contDiffWithinAt hCInfinity
        sorry

      have continuous_within_at_c: ContinuousWithinAt (iteratedDerivWithin n_x_int f (Set.Ioo c d)) (Set.Ioo c d) c := by
        apply ContDiffWithinAt.continuousWithinAt cont_diff_within_at

      have deriv_tendsto_at_a: Filter.Tendsto (iteratedDerivWithin n_x_int f (Set.Ioo c d)) (nhdsWithin c (Set.Ioo c d)) (nhds ((iteratedDerivWithin n_x_int f (Set.Ioo c d)) c)) := by
        apply ContinuousWithinAt.tendsto _
        apply continuous_within_at_c


      have deriv_zero_at_c: (iteratedDerivWithin n_x_int f (Set.Ioo c d)) c = 0 := by
        sorry


      have deriv_zero_at_d: (iteratedDerivWithin n_x_int f (Set.Ioo c d)) c = 0 := by
        sorry


      have deriv_k_const: iteratedDerivWithin n_x_int f (Set.Ioo c d) = λ y => 0 := by
        ext y
        sorry
        -- by_cases h_mem_interval: y ∈ closure (Set.Ioo c d)
        -- . sorry
        -- . by_cases n_x_int_zero: n_x_int = 0
        --   . rw [n_x_int_zero]
        --     simp


        --   . sorry

        --   have deriv_zero: derivi derivWithin_zero_of_nmem_closure h_mem_interval
        --   . simp
        --     sorry
        --   . rw [Set.eq_endpoints_or_mem_Ioo_of_mem_Icc] at y_mem_endpoints

      have deriv_within: HasDerivWithinAt (iteratedDerivWithin n_x_int f (Set.Ioo c d)) 0 (Set.Ioo c d) x := by
        --rw [hasDerivWithinAt_iff_tendsto_slope]
        sorry
      apply HasDerivWithinAt.derivWithin deriv_within
      sorry

    -- have forall_deriv_zero: ∀ (m: ℕ), m ≥ n_x_int →  ∀ (x: ℝ), x ∈ X ∩ Set.Ioo c d → (iteratedDerivWithin m f (Set.Ioo c d)) x = 0 := by
    --   intro m hm
    --   induction m with
    --   | zero => sorry
    --   | succ a ha => sorry


    have cont_diff_on: ContDiffOn ℝ ⊤ f (Set.Icc c d) := ContDiff.contDiffOn hCInfinity
    have deriv_zero_on_cd_omega: ∀ (x : ℝ), x ∈ Set.Icc c d → (iteratedDerivWithin n_x_int f (Set.Icc c d)) x = 0 := by
      intro x hx

      sorry

    have poly_on_cd: RestrictsToPoly f c d := by apply zero_deriv_implies_poly c d n_x_int c_lt_d cont_diff_on sorry -- deriv_zero_on_cd_omega
    have cd_subset_omega: Set.Ioo c d ⊆ poly_omega := by
      simp [poly_omega]
      rw [Set.subset_def]
      intro x hx
      simp only [Set.mem_sUnion]
      use Set.Ioo c d
      simp
      constructor
      exact ⟨c, d, rfl, poly_on_cd⟩
      . exact hx


    have int_subset_x_int: x_int ⊆ X ∩ e_n n_x_int := interior_subset
    have int_subset_x: x_int ⊆ X := by
      simp [Set.subset_inter_iff] at int_subset_x_int
      exact int_subset_x_int.1
    have cd_subset_x: Set.Ioo c d ⊆ X := by
      apply subset_trans cd_int int_subset_x
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
