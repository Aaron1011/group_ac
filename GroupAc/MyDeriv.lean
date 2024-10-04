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


def RestrictsToPolyOn (f: ℝ → ℝ) (s: Set ℝ) :=
  ∃ (p: Polynomial ℝ), ∀ (y: ℝ), y ∈ s → f y = p.eval y

def RestrictsToPolyBundle (f: ℝ → ℝ) (a b: ℝ) (p: Polynomial ℝ) :=
  ∀ (y: ℝ), y ∈ Set.Ioo a b → f y = p.eval y

def RestrictsToPolyBundleOn (f: ℝ → ℝ) (s: Set ℝ) (p: Polynomial ℝ) :=
  ∀ (y: ℝ), y ∈ s → f y = p.eval y

def image' {α : Type _} {β : Type _} (s : Set α) (f : (a : α) → a ∈ s → β) : Set β :=
  {b | ∃ a ha, f a ha = b}


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

lemma poly_eq_open_imp_closed (a b: ℝ) (hab: a < b) (hd: ContDiff ℝ ⊤ f) (p: Polynomial ℝ): (∀ (y: ℝ), y ∈ Set.Ioo a b → f y = p.eval y) →  (∀ (y: ℝ), y ∈ Set.Icc a b → f y = p.eval y) := by
  intro hy_open
  have eq_zero: ∀ (z: ℝ), z ∈ Set.Ioo a b → (f z - p.eval z) = 0 := by
    intro z hz
    rw [← hy_open z hz]
    simp
  have f_sub_eq_a: f a - p.eval a = 0 := by
    apply @const_ioo_implies_endpoint_left (λ z => f z - p.eval z) a b
    apply hab
    apply ContinuousOn.sub
    apply Continuous.continuousOn
    apply ContDiff.continuous hd
    exact Polynomial.continuousOn_aeval p
    apply eq_zero

  -- TODO - can we combine the above two?
  have f_sub_eq_b: f b - p.eval b = 0 := by
    apply @const_ioo_implies_endpoint_right (λ z => f z - p.eval z) a b
    apply hab
    apply ContinuousOn.sub
    apply Continuous.continuousOn
    apply ContDiff.continuous hd
    exact Polynomial.continuousOn_aeval p
    apply eq_zero

  intro y hy
  apply Set.eq_endpoints_or_mem_Ioo_of_mem_Icc at hy
  cases hy with
  | inl y_eq_a =>
    rw [y_eq_a]
    exact eq_of_sub_eq_zero f_sub_eq_a
  | inr hy' => cases hy' with
    | inl y_eq_b =>
      rw [y_eq_b]
      exact eq_of_sub_eq_zero f_sub_eq_b
    | inr y_in_ioo =>
      apply hy_open
      exact y_in_ioo


lemma zero_deriv_implies_poly (a b : ℝ) (n: ℕ) (a_lt_b: a < b) (hd: ContDiff ℝ ⊤ f) (hf: ∀ (x : ℝ), (x ∈ Set.Ioo a b) → (iteratedDeriv n f) x = 0): RestrictsToPoly f a b := by
  induction n generalizing f with
  | zero =>
    simp only [iteratedDeriv_zero] at hf
    unfold RestrictsToPoly
    use 0
    intro y hy
    simp
    apply hf
    exact hy
  | succ k hk =>
    have deriv_succ: ∀ (x: ℝ), x ∈ Set.Ioo a b → (iteratedDeriv k (deriv f)) x = 0 := by
      intro x hx
      rw [← iteratedDeriv_succ']
      apply hf
      exact hx

    have contdiff_derivative: ContDiff ℝ ⊤ (deriv f) := by
      apply ContDiff.iterate_deriv 1
      exact hd

    have deriv_f_poly: RestrictsToPoly (deriv f) a b := by
      apply hk
      apply contdiff_derivative
      exact deriv_succ

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


    have deriv_integral_eq_poly_deriv: ∀ (x: ℝ), x ∈ Set.Icc a b → deriv (fun (y : ℝ) => Polynomial.eval y poly_integral) x = Polynomial.eval x (Polynomial.derivative poly_integral) := by
      intro x _
      apply Polynomial.deriv poly_integral

    have eq_at_a: f a = Polynomial.eval a poly_integral := by
      simp [poly_integral, initial_poly_integral, poly_constant]

    have deriv_minus_is_zero: ∀y, y ∈ Set.Ioo a b → (deriv f y) - p.eval y = 0 := by
      intro y hy
      rw [hp]
      simp
      exact hy

    have deriv_minus_eq_zero_at_a: (deriv f) a - p.eval a = 0 := by
      apply @const_ioo_implies_endpoint_left (λ y => (deriv f y) - p.eval y)
      apply a_lt_b
      apply ContinuousOn.sub
      apply Continuous.continuousOn
      apply ContDiff.continuous_deriv hd
      simp
      exact Polynomial.continuousOn_aeval p
      apply deriv_minus_is_zero

    have deriv_eq_at_a: (deriv f) a = Polynomial.eval a p := by
      exact eq_of_sub_eq_zero deriv_minus_eq_zero_at_a

    have f_eq_deriv_integral: ∀(x: ℝ), x ∈ Set.Ioo a b → f x = Polynomial.eval x poly_integral := by
      intro x hx
      have eq_on_icc: ∀ y ∈ Set.Icc a b, f y = poly_integral.eval y:= by
        apply @eq_of_has_deriv_right_eq _ _ _ f
        intro q _
        have strict_deriv_at: HasStrictDerivAt f (deriv f q) q := by
          apply hd.hasStrictDerivAt
          simp
        apply HasDerivAt.hasDerivWithinAt (HasStrictDerivAt.hasDerivAt strict_deriv_at)

        intro q hq
        have temp_poly_deriv: HasDerivWithinAt (fun y ↦ Polynomial.eval y poly_integral) (Polynomial.eval q (Polynomial.derivative poly_integral)) (Set.Ici q) q := by
          apply Polynomial.hasDerivWithinAt
        rw [← deriv_integral_eq_poly_deriv] at temp_poly_deriv
        simp [deriv_integral] at temp_poly_deriv
        by_cases q_eq_a: q = a
        -- Case 1: q = a
        rw [q_eq_a]
        rw [deriv_eq_at_a]
        rw [← deriv_integral]
        apply Polynomial.hasDerivWithinAt
        -- Case 2: q ≠ a
        rw [hp]
        rw [← deriv_integral]
        apply Polynomial.hasDerivWithinAt
        apply Set.eq_left_or_mem_Ioo_of_mem_Ico at hq
        simp [q_eq_a] at hq
        simp
        exact hq

        apply Set.mem_Icc_of_Ico hq
        apply Continuous.continuousOn
        apply ContDiff.continuous hd
        apply Polynomial.continuousOn
        apply eq_at_a

      apply eq_on_icc
      apply Set.mem_Icc_of_Ioo
      exact hx

    exact ⟨poly_integral, f_eq_deriv_integral⟩

class XData (c d: ℝ) (fin_cover: Set (Set ℝ)) (f: ℝ → ℝ) :=
  (x: ℝ)
  (a: ℝ)
  (b: ℝ)
  (poly: Polynomial ℝ)
  (x_in_int : x ∈ Set.Ioo a b)
  (int_in_fin: Set.Ioo a b ∈ fin_cover)
  (poly_eq: RestrictsToPolyBundle f a b poly)

class IntervalData :=
  (i: Set ℝ)
  (poly: Polynomial ℝ)
  (poly_eq: RestrictsToPolyBundleOn f i poly)

noncomputable def x_to_data (x c d: ℝ) (fin_cover: Set (Set ℝ)) (hx: x ∈ Set.Icc c d) (h_covers_cd : Set.Icc c d ⊆ ⋃ i ∈ fin_cover, id i) (h_fin_subset : ∀ x ∈ fin_cover, ∃ a b, x = Set.Ioo a b ∧ RestrictsToPoly f a b): XData c d fin_cover f := by
  have x_in_cover: x ∈ ⋃ i ∈ fin_cover, id i := h_covers_cd hx
  rw [Set.mem_iUnion] at x_in_cover
  simp at x_in_cover
  choose i i_in_fin x_in_i using x_in_cover
  specialize h_fin_subset i i_in_fin
  choose a b hab has_ab_poly using h_fin_subset
  choose ab_poly h_ab_poly using has_ab_poly
  have i_in_fin: Set.Ioo a b ∈ fin_cover := by rwa [← hab]
  rw [hab] at x_in_i
  let x_data := XData.mk (c := c) (d := d) x a b ab_poly x_in_i i_in_fin h_ab_poly
  exact x_data

lemma x_data_preserves_x (x c d fin_cover hx h_covers_cd) (h_fin_subset) : (x_to_data (f := f) x c d fin_cover hx h_covers_cd h_fin_subset).x = x := by
  simp [x_to_data]

lemma omega_r_imp_poly (hCInfinity: ContDiff ℝ ⊤ f): ⋃₀ {i | ∃ a b, i = Set.Ioo a b ∧ RestrictsToPoly f a b} = Set.univ → ∃ p: Polynomial ℝ, f = p.eval := by
  intro omega_eq_r
  have overlap_eq: ∀ a b c d pl pr, RestrictsToPolyBundle f a b pl ∧ RestrictsToPolyBundle f c d pr → ∀x, x ∈ Set.Ioo a b ∩ Set.Ioo c d → pl = pr := by
    intro a b c d pa pb ⟨hpa, hpb⟩ x ⟨hx1, hx2⟩
    have eq_zero_intersect: ∀ y, y ∈ Set.Ioo a b ∩ Set.Ioo c d → (pa - pb).eval y = 0 := by
      intro y ⟨hy1, hy2⟩
      simp
      rw [← hpa y hy1]
      rw [← hpb y hy2]
      simp

    have intersect_infinite: (Set.Ioo a b ∩ Set.Ioo c d).Infinite := by
      rw [Set.Ioo_inter_Ioo]
      apply Set.Ioo_infinite
      simp at hx1
      simp at hx2
      rw [sup_eq_max]
      simp
      refine ⟨?_, ?_⟩
      refine ⟨?_, ?_⟩
      linarith
      linarith
      refine ⟨?_, ?_⟩
      linarith
      linarith

    have diff_zero_all: (pa - pb) = 0 := by
      obtain ⟨nplusone_zeros, zeros_subset, zeros_card⟩ := @Set.Infinite.exists_subset_card_eq _ (Set.Ioo a b ∩ Set.Ioo c d) intersect_infinite ((pa - pb).natDegree + 1)
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (pa - pb) nplusone_zeros
      intro y hy
      simp only [Set.subset_def] at zeros_subset
      have y_in_intersect: y ∈ Set.Ioo a b ∩ Set.Ioo c d := by
        exact zeros_subset y hy
      apply eq_zero_intersect
      apply y_in_intersect
      rw [zeros_card]
      simp

    simp at diff_zero_all
    apply eq_of_sub_eq_zero diff_zero_all

  let all_intervals := {i | ∃ a b, i = Set.Ioo a b ∧ RestrictsToPoly f a b}
  let all_union := ⋃₀ all_intervals
  have all_open: ∀ s, s ∈ all_intervals → IsOpen (id s) := by
    intro s hs
    simp [all_intervals] at hs
    obtain ⟨a, b, hab, h⟩ := hs
    simp
    rw [hab]
    apply isOpen_Ioo


  have poly_on_closed: ∀ c d, c < d →  RestrictsToPoly f c d := by
    intro c d c_lt_d
    have cd_subset: Set.Icc c d ⊆ ⋃ i ∈ all_intervals, id i := by
      simp only [all_union, all_intervals]
      simp only [id]
      rw [← Set.sUnion_eq_biUnion]
      rw [omega_eq_r]
      simp

    have cd_compact: IsCompact (Set.Icc c d) := by
      apply isCompact_Icc
    obtain ⟨fin_cover, h_fin_subset, h_fin_cover_finite, h_covers_cd⟩ := IsCompact.elim_finite_subcover_image cd_compact all_open cd_subset
    rw [Set.subset_def] at h_fin_subset
    simp only [all_intervals] at h_fin_subset
    simp only [Set.mem_setOf_eq] at h_fin_subset

    have interval_to_poly: ∀ i ∈ fin_cover, RestrictsToPolyOn f i := by
      intro i a_in_fin
      specialize h_fin_subset i a_in_fin
      choose a' b' hab has_ab_poly using h_fin_subset
      rw [RestrictsToPolyOn]
      rw [RestrictsToPoly] at has_ab_poly
      obtain ⟨p, hp⟩ := has_ab_poly
      rw [← hab] at hp
      exact ⟨p, hp⟩

    let interval_to_poly := (fun i hi => by
      -- CANNOT use 'obtain' here: see https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Problems.20with.20obtain/near/467580722
      exact IntervalData.mk i (Classical.choose (interval_to_poly i hi)) (Classical.choose_spec (interval_to_poly i hi))
    )

    let polys_from_intervals := (λ d => d.poly) '' (image' fin_cover interval_to_poly)
    have polys_from_intervals_finite: polys_from_intervals.Finite := by
      simp only [polys_from_intervals, image']
      apply Set.Finite.image
      exact Set.Finite.dependent_image h_fin_cover_finite interval_to_poly

    let new_all_degrees := Polynomial.natDegree '' polys_from_intervals
    have new_all_degrees_finite: new_all_degrees.Finite := by
      exact Set.Finite.image (fun p ↦ p.natDegree) polys_from_intervals_finite
    have ⟨new_all_degrees_finset, h_new_all_degrees_finset⟩ := Set.Finite.exists_finset new_all_degrees_finite
    have new_all_degrees_finset_nonempty: new_all_degrees_finset.Nonempty := by
      let p := (c + d) / 2
      have p_in_cd: p ∈ Set.Icc c d := by
        simp [p]
        refine ⟨?_, ?_⟩
        linarith
        linarith
      have p_in_union: p ∈ ⋃ i ∈ fin_cover, id i := by
        apply h_covers_cd p_in_cd
      rw [Set.mem_iUnion] at p_in_union
      obtain ⟨i, hi⟩ := p_in_union
      simp at hi
      obtain ⟨i_in_fin, p_in_i⟩ := hi
      let i_data := interval_to_poly i i_in_fin
      rw [Finset.Nonempty]
      use i_data.poly.natDegree
      rw [h_new_all_degrees_finset]
      simp only [new_all_degrees]
      simp
      use i_data.poly
      simp
      simp [polys_from_intervals]
      simp only [image']
      simp
      use i_data
      simp
      use i
      use i_in_fin


    let max_degree := Finset.max' new_all_degrees_finset new_all_degrees_finset_nonempty
    let large_degree := max_degree + 1

    have fn_zero: ∀ (x: ℝ), x ∈ Set.Icc c d → (iteratedDeriv large_degree f) x = 0 := by
      intro x hx

      have x_in_union: x ∈ ⋃ i ∈ fin_cover, id i := by
        apply h_covers_cd hx
      rw [Set.mem_iUnion] at x_in_union
      obtain ⟨i, hi⟩ := x_in_union
      simp at hi
      obtain ⟨i_in_fin, x_in_i⟩ := hi
      obtain ⟨a, b, i_eq_ab, h_ab_poly⟩ := h_fin_subset i i_in_fin
      rw [RestrictsToPoly] at h_ab_poly
      let i_data := interval_to_poly i i_in_fin
      have i_data_i_eq: i_data.i = i := by
        simp [i_data, interval_to_poly]
      rw [i_eq_ab] at x_in_i


      have derivwith_eq: Set.EqOn (iteratedDerivWithin large_degree f (Set.Ioo a b)) (iteratedDerivWithin large_degree i_data.poly.eval (Set.Ioo a b)) (Set.Ioo a b) := by
        apply iteratedDerivWithin_congr
        apply uniqueDiffOn_Ioo
        rw [Set.EqOn]
        let poly_eq := i_data.poly_eq
        simp [RestrictsToPolyBundleOn] at poly_eq
        intro z hz
        specialize poly_eq z
        rw [i_data_i_eq] at poly_eq
        rw [i_eq_ab] at poly_eq
        apply poly_eq hz



      specialize derivwith_eq
      rw [Set.EqOn] at derivwith_eq
      specialize derivwith_eq x_in_i
      rw [iteratedDerivWithin] at derivwith_eq
      rw [iteratedDeriv]

      have eq_normal_deriv: Set.EqOn ((iteratedFDerivWithin ℝ large_degree f (Set.Ioo a b))) ((iteratedFDeriv ℝ large_degree f)) (Set.Ioo a b) := by
        apply iteratedFDerivWithin_of_isOpen large_degree (isOpen_Ioo)

      rw [iteratedDerivWithin] at derivwith_eq
      rw [iteratedFDerivWithin_of_isOpen large_degree (isOpen_Ioo) x_in_i] at derivwith_eq
      rw [iteratedFDerivWithin_of_isOpen large_degree (isOpen_Ioo) x_in_i] at derivwith_eq
      rw [← iteratedDeriv] at derivwith_eq
      rw [← iteratedDeriv] at derivwith_eq
      rw [← iteratedDeriv]
      rw [derivwith_eq]
      have ab_degree_in: i_data.poly.natDegree ∈ new_all_degrees_finset := by
        rw [h_new_all_degrees_finset]
        simp only [new_all_degrees]
        simp [polys_from_intervals]
        simp only [image']
        simp
        use i_data
        simp
        use i
        use i_in_fin

      have ab_poly_le_max': i_data.poly.natDegree ≤ max_degree := by
        exact Finset.le_max' new_all_degrees_finset i_data.poly.natDegree ab_degree_in

      have degree_lt: i_data.poly.natDegree < large_degree := by
        simp only [large_degree]
        linarith


      have deriv_fun_eq: deriv (fun (p : ℝ) => Polynomial.eval p i_data.poly) = (fun (p: ℝ) => Polynomial.eval p (Polynomial.derivative i_data.poly)) := by
        ext
        simp

      have iterated_deriv_fun_eq: ∀ (n: ℕ), iteratedDeriv n (fun (p : ℝ) => Polynomial.eval p i_data.poly) = (fun (p: ℝ) => Polynomial.eval p (Polynomial.derivative^[n] i_data.poly)) := by
        intro n
        induction n with
        | zero =>
          simp
        | succ k ih =>
          simp
          rw [iteratedDeriv_succ]
          rw [ih]
          ext p
          simp only [Polynomial.deriv]
          simp [← Function.iterate_succ_apply']



      rw [iterated_deriv_fun_eq]
      rw [Polynomial.iterate_derivative_eq_zero degree_lt]
      simp
    apply zero_deriv_implies_poly c d large_degree c_lt_d hCInfinity
    intro y hy
    apply fn_zero
    exact Set.mem_Icc_of_Ioo hy
  obtain ⟨p_zero_one, h_p_zero_one⟩ := by apply poly_on_closed 0 1 zero_lt_one
  use p_zero_one
  by_contra!
  simp [Function.ne_iff] at this
  obtain ⟨bad_x, h_bad_x⟩ := this

  -- Obtain an interval enclosing both [0, 1] and our bad point
  let enclosing := Set.Icc (min bad_x 0) (max bad_x 1)
  let enclosing_open := Set.Ioo (min bad_x 0) (max bad_x 1)
  have min_lt_max: (min bad_x 0) < (max bad_x 1) := by
    simp

  obtain ⟨p_enclosing, h_p_enclosing⟩ := by apply poly_on_closed (min bad_x 0) (max bad_x 1) min_lt_max
  -- TODO - deduplicate this
  have intersect_infinite: (enclosing_open ∩ Set.Ioo 0 1).Infinite := by
    rw [Set.Ioo_inter_Ioo]
    apply Set.Ioo_infinite
    simp

  have diff_zero_all: (p_enclosing - p_zero_one) = 0 := by
    obtain ⟨nplusone_zeros, zeros_subset, zeros_card⟩ := @Set.Infinite.exists_subset_card_eq _ (enclosing_open ∩ Set.Ioo 0 1) intersect_infinite ((p_enclosing - p_zero_one).natDegree + 1)
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (p_enclosing - p_zero_one) nplusone_zeros
    intro y hy
    simp only [Set.subset_def] at zeros_subset
    have y_in_intersect: y ∈ enclosing_open ∩ Set.Ioo 0 1 := by
      simp only [enclosing_open]
      have y_in_closed := zeros_subset y hy
      simp only [enclosing_open] at y_in_closed
      exact y_in_closed


    have eq_zero_intersect: ∀ z, z ∈ enclosing_open ∩ Set.Ioo 0 1 → (p_enclosing - p_zero_one).eval z = 0 := by
      intro z ⟨hz1, hz2⟩
      simp only [enclosing_open] at hz1
      simp
      rw [← h_p_enclosing z hz1]
      rw [← h_p_zero_one z hz2]
      simp

    apply eq_zero_intersect
    apply y_in_intersect
    rw [zeros_card]
    simp





  have eq_poly: p_enclosing = p_zero_one := by apply eq_of_sub_eq_zero diff_zero_all
  apply poly_eq_open_imp_closed at h_p_enclosing
  rw [h_p_enclosing, eq_poly] at h_bad_x
  simp at h_bad_x
  simp
  simp
  exact hCInfinity



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


  let e_n := fun k => { x: ℝ | (iteratedDeriv k f) x = 0 }
  have en_closed: ∀ k: ℕ, IsClosed (e_n k) := by
    intro k
    simp only [e_n]
    --have closed_zero: IsClosed { @Set.Icc _ _ 0 0 } := sorry
    simp [← Set.mem_singleton_iff]
    rw [← Set.preimage]
    apply IsClosed.preimage
    -- refine Continuous.comp' ?_ ?_
    --apply Continuous.comp
    --apply continuous_subtype_val
    apply ContDiff.continuous_iteratedDeriv k hCInfinity _
    exact OrderTop.le_top _
    exact isClosed_singleton
    --dsimp [ab_subspace]
    --sorry
    --apply continuous_id'

  obtain ⟨poly_intervals, hIntervals⟩ := TopologicalSpace.IsTopologicalBasis.open_eq_sUnion Real.isTopologicalBasis_Ioo_rat poly_open
  have unique_diff: ∀ (x c d: ℝ), x ∈ Set.Ioo c d → UniqueDiffWithinAt ℝ (Set.Ioo c d) x := by
    exact fun x c d a ↦ uniqueDiffWithinAt_Ioo a


  -- LEAN BUG - try moving this into a 'have' block that already contains errors
  have r_closed: OrderClosedTopology ℝ := by
    apply NormedLatticeAddCommGroup.orderClosedTopology
  --have nonempty_closed_interval: ∀ a b : ℝ, a < b → ((Set.Icc a b) ∩ poly_omega).Nonempty := by
  have nonempty_closed_interval: ∀ a b : ℝ, a < b → ((Set.Icc a b) ∩ poly_omega).Nonempty := by
    intro a b a_lt_b

    --have ab_topology: TopologicalSpace { x: ℝ // x ∈ Set.Icc a b } := by
    --  exact instTopologicalSpaceSubtype

    let ab_subspace :=  { x: ℝ // x ∈ Set.Icc a b }

    have a_in_subtype: a ∈ Set.Icc a b := by
      simp
      linarith


    have b_in_subtype: b ∈ Set.Icc a b := by
      simp
      linarith

    have ab_subspace_enk_eq : ∀ k: ℕ, ({x : ab_subspace | x.1 ∈ (e_n k)}) = (Set.Icc a b) ∩ e_n k := by
      intro k
      ext p
      refine ⟨?_, ?_⟩
      intro p_in_val
      simp at p_in_val
      simp
      refine ⟨p_in_val.2, p_in_val.1⟩

      intro p_in_intersect
      simp
      simp at p_in_intersect
      exact ⟨p_in_intersect.2, p_in_intersect.1⟩


    have en_closed_subtype: ∀ k: ℕ, IsClosed ({x : ab_subspace | x.1 ∈ e_n k}) := by
      intro k
      specialize ab_subspace_enk_eq k
      sorry





    have en_intersect_closed: ∀ k: ℕ , IsClosed (X := ab_subspace) ((Set.Icc ⟨a, a_in_subtype⟩ ⟨b, b_in_subtype⟩) ∩ {x: { x: ℝ // x ∈ Set.Icc a b } | x.1 ∈ e_n k }) := by
      intro k
      apply IsClosed.inter
      apply isClosed_Icc
      apply en_closed_subtype k


    have en_covers: (@Set.univ ab_subspace) = Set.iUnion fun j => (Set.Icc ⟨a, a_in_subtype⟩ ⟨b, b_in_subtype⟩ ∩ ({x: ab_subspace | x.1 ∈ e_n j})) := by
      ext p
      obtain ⟨n, hn⟩ := hf p
      have p_in_en: p.1 ∈ (e_n n) := by
        simp only [e_n]
        simp
        exact hn


      --have p_implies_in_en: fun h_new => (p ∈ (e_n n) (e_n n) ∩ Set.Icc a b) := by
      --  simp only [e_n]
      --  apply And.intro p_in_en h_new

      constructor
      -- first case
      intro p_in_interval
      have p_in_intersect: p.1 ∈ (e_n n) ∩ Set.Icc a b := by
        apply Set.mem_inter
        exact p_in_en
        obtain ⟨real_p, hp⟩ := p
        exact hp


      simp only [Set.mem_iUnion]
      use n
      obtain ⟨real_p, hp⟩ := p
      refine ⟨hp, ?_⟩
      simp at p_in_intersect
      simp
      exact p_in_intersect.1

      -- second case

      simp

    have nonempty: (Set.Icc a b).Nonempty := by
      rw [Set.nonempty_Icc]
      linarith



    have real_nonempty: Nonempty (Set.Icc a b) := by
      rw [Set.nonempty_iff_ne_empty']
      exact Set.nonempty_iff_ne_empty.mp nonempty


    have nontrivial_ab: Nontrivial ab_subspace := by
      rw [nontrivial_iff]
      use ⟨a, a_in_subtype⟩
      use ⟨b, b_in_subtype⟩
      exact ne_of_lt a_lt_b


    --obtain ⟨interior_index, int_nonempty⟩ := @nonempty_interior_of_iUnion_of_closed (Set.Icc a b) _ _ _ _ _ _ en_intersect_closed en_covers
    -- TODO - we need to apply this to an entire topolgical space. We need [a, b] with the subspace topology
    -- Apply Baire category theorem
    obtain ⟨interior_index, int_nonempty⟩ := nonempty_interior_of_iUnion_of_closed en_intersect_closed en_covers.symm
    have int_open: IsOpen (interior ({x: ab_subspace | x.1 ∈ Set.Icc a b ∩ e_n interior_index})) := by apply isOpen_interior
    obtain ⟨c, d, c_lt_d, cd_int⟩ := IsOpen.exists_Ioo_subset int_open int_nonempty
    have _: a ≤ c.1 := by
      obtain ⟨c_val, hc⟩ := c
      simp
      simp [Set.mem_Iic] at hc
      linarith

    have _: d.1 ≤ b := by
      obtain ⟨d_val, hd⟩ := d
      simp
      simp [Set.mem_Iic] at hd
      linarith

    have cd_int_imp_ab: ∀ y: ab_subspace, y ∈ Set.Ioo c d → y.1 ∈ Set.Icc a b := by
      intro y hy
      rw [Set.subset_def] at cd_int
      specialize cd_int y hy
      simp only [mem_interior] at cd_int
      simp only [Set.subset_def] at cd_int
      obtain ⟨t, ht, h_other_t, y_in_t⟩ := cd_int
      specialize ht y y_in_t
      simp only [Set.mem_setOf_eq] at ht
      exact ht.1

    have cd_subset_ab: Set.Ioo c.1 d.1 ⊆ Set.Icc a b := by
      rw [Set.subset_def]
      intro y hy
      simp
      simp at hy
      refine ⟨?_, ?_⟩
      linarith
      linarith

    have int_subset_a_b: interior (Set.Icc a b ∩ e_n interior_index) ⊆ Set.Icc a b := by
      rw [Set.subset_def]
      intro y hy
      simp only [mem_interior] at hy
      simp only [Set.subset_def] at hy
      obtain ⟨t, ht, h_other_t, y_in_t⟩ := hy
      specialize ht y y_in_t
      exact ht.1


    have cont_diff_on: ContDiffOn ℝ ⊤ f (Set.Icc c d) := ContDiff.contDiffOn hCInfinity
    have zero_on_cd: ∀ (x: ℝ), x ∈ (Set.Ioo c.1 d.1) → (iteratedDeriv interior_index f) x = 0 := by
      intro x x_in_cd
      simp at cd_int

      have x_in_ab: x ∈ Set.Icc a b := by
        apply cd_subset_ab x_in_cd

      dsimp [e_n] at cd_int
      simp only [Set.subset_def] at cd_int
      simp only [mem_interior] at cd_int
      simp only [Set.subset_def] at cd_int
      simp only [Set.mem_setOf_eq] at cd_int
      let x_subspace: ab_subspace := ⟨x, x_in_ab⟩
      have x_subspace_in: x_subspace ∈ Set.Ioo c d := by
        simp
        exact x_in_cd

      have iter_x: (∀x, x ∈ Set.Ioo c.1 d.1 → iteratedDeriv interior_index f x = 0) := by
        intro new_x new_x_cd
        let new_x_subspace: ab_subspace := ⟨new_x, cd_subset_ab new_x_cd⟩
        obtain ⟨other_t, other_ht, other_t_isopen, x_in_other_t⟩ := cd_int new_x_subspace new_x_cd
        apply other_ht new_x_subspace
        obtain ⟨new_x_cd_int⟩ := cd_int new_x_subspace new_x_cd
        obtain ⟨iter_val, h_iter_val⟩ := cd_int new_x_subspace new_x_cd
        exact x_in_other_t


      specialize iter_x x_subspace
      rw [iteratedDeriv]
      rw [iteratedDeriv] at iter_x
      have derives_eq: Set.EqOn (iteratedFDerivWithin ℝ interior_index f (Set.Ioo c d)) (iteratedFDeriv ℝ interior_index f) (Set.Ioo c d) :=
         by apply iteratedFDerivWithin_of_isOpen interior_index (isOpen_Ioo)
      rw [Set.EqOn] at derives_eq
      simp

      have zero_on_open: (iteratedFDeriv ℝ interior_index f) x (fun x ↦ 1) = 0 := by
        simp only [derives_eq]
        specialize derives_eq x_in_cd
        apply iter_x
        exact x_subspace_in

      apply zero_on_open

    have poly_on_cd: RestrictsToPoly f c d := by apply zero_deriv_implies_poly c d interior_index c_lt_d hCInfinity zero_on_cd
    have cd_subset_omega: Set.Ioo c.1 d.1 ⊆ poly_omega := by
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

    have cd_subet_omega_ab: Set.Ioo c.1 d.1 ⊆ (Set.Icc a b) ∩ poly_omega := by
      apply Set.subset_inter
      apply cd_subset_ab
      apply cd_subset_omega


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
      apply c_lt_d

    rw [Set.nonempty_def] at cd_nonempty
    obtain ⟨elem_cd, h_elem_cd⟩ := cd_nonempty

    have elem_target: elem_cd.1 ∈ (Set.Icc a b) ∩ poly_omega := by
      rw [Set.subset_def] at cd_subet_omega_ab
      apply cd_subet_omega_ab elem_cd _
      simp
      simp at h_elem_cd
      apply h_elem_cd

    exact ⟨elem_cd, elem_target⟩


  let X := poly_omegaᶜ
  have X_closed: IsClosed X := IsOpen.isClosed_compl poly_open
  have X_empty: X = ∅ := by
    have x_accum: ∀ x, x ∈ X → AccPt x (Filter.principal X) := by
      by_contra!
      obtain ⟨x, ⟨x_in, x_not_acc⟩⟩ := this
      rw [accPt_iff_nhds] at x_not_acc
      simp at x_not_acc
      obtain ⟨u, hu_neighbor, hu_singleton⟩ := x_not_acc
      obtain ⟨g, h, x_in_gh, gh_in_u⟩ := mem_nhds_iff_exists_Ioo_subset.mp hu_neighbor

      have gh_nonempty: Set.Nonempty (Set.Ioo g h) := by
        rw [Set.nonempty_def]
        use x

      have g_lt_h: g < h := by
        apply Set.nonempty_Ioo.mp gh_nonempty

      have g_lt_x: g < x := by
        simp [Set.mem_Ioo] at x_in_gh
        exact x_in_gh.1

      have x_lt_h: x < h := by
        simp [Set.mem_Ioo] at x_in_gh
        exact x_in_gh.2

      have left_y_omega: ∀ y: ℝ, y ∈ (Set.Ioo g x) → y ∈ poly_omega := by
        intro y hy
        have y_neq_x: y ≠ x := by
          simp [Set.mem_Ioo] at hy
          linarith
        have y_in_u: y ∈ u := by
          apply gh_in_u
          simp
          simp at hy
          refine ⟨hy.1, ?_⟩
          linarith

        have y_notin_x: y ∉ X := by
          specialize hu_singleton y y_in_u
          rw [← not_imp_not] at hu_singleton
          simp at y_neq_x
          apply hu_singleton y_neq_x

        rw [Set.mem_compl_iff] at y_notin_x
        simp at y_notin_x
        exact y_notin_x

      -- TODO - can we do something like `wlog` to combine this with the above 'g x' case?
      have right_y_omega: ∀ y: ℝ, y ∈ (Set.Ioo x h) → y ∈ poly_omega := by
        intro y hy
        have y_neq_x: y ≠ x := by
          simp [Set.mem_Ioo] at hy
          linarith
        have y_in_u: y ∈ u := by
          apply gh_in_u
          simp
          simp at hy
          refine ⟨?_, hy.2⟩
          linarith

        have y_notin_x: y ∉ X := by
          specialize hu_singleton y y_in_u
          rw [← not_imp_not] at hu_singleton
          simp at y_neq_x
          apply hu_singleton y_neq_x

        rw [Set.mem_compl_iff] at y_notin_x
        simp at y_notin_x
        exact y_notin_x

      have left_subset_omega: Set.Ioo g x ⊆ poly_omega := by
        rw [Set.subset_def]
        apply left_y_omega

      have right_subset_omega: Set.Ioo x h ⊆ poly_omega := by
        rw [Set.subset_def]
        apply right_y_omega

      -- TODO we need to have poly_omega as a union of disjoint open intervals
      --obtain ⟨leftPoly, h_leftPoly⟩ := left_subset_omega

      -- TODO - get this intervals from the fact that x is an isolated point
      --have _: (Set.Ioo g x) ⊆ poly_omega := by sorry
      --have _: (Set.Ioo x h) ⊆ poly_omega := by sorry

      have is_first_poly: RestrictsToPoly f g x := by sorry
      have is_second_poly: RestrictsToPoly f x h := by sorry

      obtain ⟨first_poly, h_first_poly⟩ := is_first_poly
      obtain ⟨second_poly, h_second_poly⟩ := is_second_poly

      let n := max first_poly.natDegree second_poly.natDegree
      have zero_on_new: ∀ (y: ℝ), y ∈ (Set.Ioo g h) → (iteratedDeriv (n + 1) f) y = 0 := by
        have orig_first_degree_zero: ((⇑Polynomial.derivative)^[n] first_poly).natDegree ≤ first_poly.natDegree - n := by
          apply Polynomial.natDegree_iterate_derivative first_poly n
        simp at orig_first_degree_zero
        have first_le_n : first_poly.natDegree ≤ n := by exact Nat.le_max_left first_poly.natDegree second_poly.natDegree
        have first_degree_zero': ((⇑Polynomial.derivative)^[n] first_poly).natDegree - (first_poly.natDegree - n) = 0 := by
          apply tsub_eq_zero_of_le orig_first_degree_zero
        have first_degree_zero: ((⇑Polynomial.derivative)^[n] first_poly).natDegree = 0 := by
          simp [n] at first_degree_zero'
          linarith

        -- FIXME - remove copy-paste with 'orig_first_degree_zero' code above
        have orig_second_degree_zero: ((⇑Polynomial.derivative)^[n] second_poly).natDegree ≤ second_poly.natDegree - n := by
          apply Polynomial.natDegree_iterate_derivative second_poly n
        simp at orig_second_degree_zero
        have second_le_n : second_poly.natDegree ≤ n := by exact Nat.le_max_right first_poly.natDegree second_poly.natDegree
        have second_degree_zero': ((⇑Polynomial.derivative)^[n] second_poly).natDegree - (second_poly.natDegree - n) = 0 := by
          apply tsub_eq_zero_of_le orig_second_degree_zero
        have second_degree_zero: ((⇑Polynomial.derivative)^[n] second_poly).natDegree = 0 := by
          simp [n] at second_degree_zero'
          linarith

        have first_zero: (Polynomial.derivative ((⇑Polynomial.derivative)^[n] first_poly)) = 0 := by
          apply Polynomial.derivative_of_natDegree_zero first_degree_zero

        have first_zero_within: ∀y, y ∈ Set.Ioo g x → (Polynomial.derivative ((⇑Polynomial.derivative)^[n] first_poly)).eval y = 0 := by
          intro y hy
          simp [first_zero]

        have second_zero: (Polynomial.derivative ((⇑Polynomial.derivative)^[n] second_poly)) = 0 := by
          apply Polynomial.derivative_of_natDegree_zero second_degree_zero

        have second_zero_within: ∀y, y ∈ Set.Ioo g x → (Polynomial.derivative ((⇑Polynomial.derivative)^[n] second_poly)).eval y = 0 := by
          intro y hy
          simp [second_zero]

        --have zero_at_x: Polynomial.eval x (Polynomial.derivative ((⇑Polynomial.derivative)^[n] first_poly)) = 0 := by
        --  apply @const_ioo_implies_endpoint_right (λ y => Polynomial.eval y (Polynomial.derivative ((⇑Polynomial.derivative)^[n] first_poly))) g x 0
        --   apply g_lt_x
        --   apply Polynomial.continuousOn
        --   apply first_zero_within

        -- have zero_at_x: Polynomial.eval x (Polynomial.derivative ((⇑Polynomial.derivative)^[n] first_poly)) = 0 := by
        --   apply @const_ioo_implies_endpoint_right (λ y => Polynomial.eval y (Polynomial.derivative ((⇑Polynomial.derivative)^[n] first_poly))) g x 0
        --   apply g_lt_x
        --   apply Polynomial.continuousOn
        --   apply first_zero_within

        have f_deriv_zero: ∀ (y: ℝ), y ∈ (Set.Ioo g x ∪ Set.Ioo x h) → (iteratedDeriv (n + 1) f) y = 0 := by
          intro y hy
          rw [Set.mem_union] at hy
          cases hy with
          | inl y_in_left =>
            have y_eq_eval: f y = first_poly.eval y := by
              apply h_first_poly
              exact y_in_left
            rw [iteratedDeriv_succ]
            sorry

          | inr y_in_right =>
            sorry

        -- Use continuity here
        have f_deriv_at_x: (iteratedDeriv (n + 1) f) x = 0 := by
          apply const_ioo_implies_endpoint_right g x 0 g_lt_x _
          have zero_on_interval: ∀ (y: ℝ), y ∈ Set.Ioo g x → (iteratedDeriv (n + 1) f) y = 0 := by
            intro y hy
            have y_in_union: y ∈ (Set.Ioo g x ∪ Set.Ioo x h) := by
              rw [Set.mem_union]
              left
              exact hy
            apply f_deriv_zero y y_in_union
          intro z hz
          apply zero_on_interval z hz
          apply (ContDiff.continuous_iteratedDeriv _ hCInfinity _).continuousOn
          simp


        -- f^(n) is zero on (g, x) and (x, h), and x, so it's zero on (g, h)
        have f_zero_full: ∀ (y: ℝ), y ∈ (Set.Ioo g h) → (iteratedDeriv (n + 1) f) y = 0 := sorry
        exact f_zero_full

      have f_poly_full: RestrictsToPoly f g h := by
        apply zero_deriv_implies_poly
        apply g_lt_h
        assumption
        apply zero_on_new

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
    -- Apply baire category theorem again
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
    have deriv_zero_on_cd_omega: ∀ (x : ℝ), x ∈ Set.Ioo c d → (iteratedDeriv n_x_int f) x = 0 := by
      intro x hx

      sorry

    have poly_on_cd: RestrictsToPoly f c d := by apply zero_deriv_implies_poly c d n_x_int c_lt_d hCInfinity deriv_zero_on_cd_omega
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

  obtain ⟨the_final_poly, h_the_final_poly⟩ := omega_r_imp_poly (f := f) hCInfinity poly_full
  simp only [RestrictsToPoly]
  use the_final_poly
  intro z hz
  rw [h_the_final_poly]
