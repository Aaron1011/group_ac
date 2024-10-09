
import Paperproof
import Mathlib
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.Basic

open Topology
open Filter

-- set_option profiler true
-- set_option maxHeartbeats 1000000


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


-- TODO - factor this out and maybe pr to mathlib
lemma icc_not_open: ∀ a b: ℝ, a ≤ b → ¬ IsOpen (Set.Icc a b) := by
  intro a b a_le_b
  have is_closed: IsClosed (Set.Icc a b) := isClosed_Icc
  have nonempty: (Set.Icc a b).Nonempty := by
    refine Set.nonempty_Icc.mpr a_le_b

  have icc_missing: (b + 1) ∉ Set.Icc a b := by
    simp

  have icc_not_univ: Set.Icc a b ≠ Set.univ := by
    rw [Set.ne_univ_iff_exists_not_mem]
    refine ⟨b + 1, icc_missing⟩

  have not_clopen: ¬IsClopen (Set.Icc a b) := by
    apply (not_imp_not.mpr isClopen_iff.mp)
    simp
    refine ⟨Set.Nonempty.ne_empty nonempty, icc_not_univ⟩

  simp [IsClopen] at not_clopen
  apply not_clopen is_closed

lemma ici_not_open: ∀ a: ℝ, ¬ IsOpen (Set.Ici a) := by
  intro a
  have is_closed: IsClosed (Set.Ici a) := isClosed_Ici
  have nonempty: (Set.Ici a).Nonempty := by simp
  have ici_missing: (a - 1) ∉ Set.Ici a := by
    simp

  have ici_not_univ: Set.Ici a ≠ Set.univ := by
    rw [Set.ne_univ_iff_exists_not_mem]
    refine ⟨a - 1, ici_missing⟩

  have not_clopen: ¬IsClopen (Set.Ici a) := by
    apply (not_imp_not.mpr isClopen_iff.mp)
    simp
    refine ⟨Set.Nonempty.ne_empty nonempty, ici_not_univ⟩

  simp [IsClopen] at not_clopen
  apply not_clopen is_closed

-- TODO - deduplicate with ici
lemma iic_not_open: ∀ a: ℝ, ¬ IsOpen (Set.Iic a) := by
  intro a
  have is_closed: IsClosed (Set.Iic a) := isClosed_Iic
  have nonempty: (Set.Iic a).Nonempty := by simp
  have iic_missing: (a + 1) ∉ Set.Iic a := by
    simp

  have ici_not_univ: Set.Iic a ≠ Set.univ := by
    rw [Set.ne_univ_iff_exists_not_mem]
    refine ⟨a + 1, iic_missing⟩

  have not_clopen: ¬IsClopen (Set.Iic a) := by
    apply (not_imp_not.mpr isClopen_iff.mp)
    simp
    refine ⟨Set.Nonempty.ne_empty nonempty, ici_not_univ⟩

  simp [IsClopen] at not_clopen
  apply not_clopen is_closed

lemma ico_not_open: ∀ a b: ℝ, a < b → ¬ IsOpen (Set.Ico a b) := by
  intro a b a_lt_b
  have frontier_eq: frontier (Set.Ico a b) = {a, b} := by apply frontier_Ico a_lt_b
  have frontier_imp_not_open: ¬((Set.Ico a b) ∩ frontier (Set.Ico a b) = ∅) → ¬ IsOpen (Set.Ico a b) := not_imp_not.mpr IsOpen.inter_frontier_eq
  have a_in_ico: a ∈ Set.Ico a b := by
    rw [Set.mem_Ico]
    refine ⟨?_, a_lt_b⟩
    simp
  have intersect_frontier: a ∈ (Set.Ico a b) ∩ frontier (Set.Ico a b) := by
    rw [frontier_eq]
    simp [a_in_ico]

  have frontier_intersect_nonempty: Set.Nonempty ((Set.Ico a b) ∩ frontier (Set.Ico a b)):= by
    refine ⟨a, intersect_frontier⟩

  have not_eq_empty: ¬((Set.Ico a b) ∩ frontier (Set.Ico a b) = ∅) := by
    exact Set.nonempty_iff_ne_empty.mp frontier_intersect_nonempty

  apply frontier_imp_not_open not_eq_empty

-- TODO: deduplicate with ico
lemma ioc_not_open: ∀ a b: ℝ, a < b → ¬ IsOpen (Set.Ioc a b) := by
  intro a b a_lt_b
  have frontier_eq: frontier (Set.Ioc a b) = {a, b} := by apply frontier_Ioc a_lt_b
  have frontier_imp_not_open: ¬((Set.Ioc a b) ∩ frontier (Set.Ioc a b) = ∅) → ¬ IsOpen (Set.Ioc a b) := not_imp_not.mpr IsOpen.inter_frontier_eq
  have b_in_ioc: b ∈ Set.Ioc a b := by
    rw [Set.mem_Ioc]
    refine ⟨a_lt_b, ?_⟩
    simp
  have intersect_frontier: b ∈ (Set.Ioc a b) ∩ frontier (Set.Ioc a b) := by
    rw [frontier_eq]
    simp [b_in_ioc]

  have frontier_intersect_nonempty: Set.Nonempty ((Set.Ioc a b) ∩ frontier (Set.Ioc a b)):= by
    refine ⟨b, intersect_frontier⟩

  have not_eq_empty: ¬((Set.Ioc a b) ∩ frontier (Set.Ioc a b) = ∅) := by
    exact Set.nonempty_iff_ne_empty.mp frontier_intersect_nonempty

  apply frontier_imp_not_open not_eq_empty




lemma iter_deriv_degree_zero (n: ℕ) (p: Polynomial ℝ) (hp: p.degree = n): ((⇑Polynomial.derivative)^[n] p).degree = 0 := by
  induction n generalizing p with
  | zero =>
    exact hp
  | succ k ih =>
    simp only [Function.iterate_succ]
    have deriv_degree_k: (Polynomial.derivative p).degree = k := by
      rw [Polynomial.degree_eq_iff_natDegree_eq_of_pos] at hp
      have natdegree_gt_zero: 0 < p.natDegree := by
        linarith
      rw [Polynomial.degree_derivative_eq p natdegree_gt_zero]
      simp
      apply Nat.sub_eq_of_eq_add
      exact hp
      simp
    apply ih (Polynomial.derivative p) deriv_degree_k




lemma iterated_deriv_eq_f_poly (n: ℕ) (p: Polynomial ℝ) (s: Set ℝ) (hs: UniqueDiffOn ℝ s) (ho: IsOpen s) (hp: RestrictsToPolyBundleOn f s p): Set.EqOn (iteratedDeriv n f) (iteratedDeriv n p.eval) s := by
  rw [Set.EqOn]
  intro x hx
  rw [iteratedDeriv]
  rw [iteratedDeriv]
  rw [←iteratedFDerivWithin_of_isOpen n ho]
  rw [←iteratedFDerivWithin_of_isOpen n ho]
  simp only [iteratedDerivWithin_eq_iterate hs hx]
  apply iteratedDerivWithin_congr hs
  rw [Set.EqOn]
  simp [RestrictsToPolyBundleOn] at hp
  intro z hz
  specialize hp z
  exact hp hz
  exact hx
  exact hx
  exact hx

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

lemma poly_iterated_deriv (n: ℕ) (p: Polynomial ℝ): iteratedDeriv n (fun (x : ℝ) => Polynomial.eval x p) = (fun (x: ℝ) => Polynomial.eval x (Polynomial.derivative^[n] p)) := by
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

class IntervalData :=
  (i: Set ℝ)
  (poly: Polynomial ℝ)
  (poly_eq: RestrictsToPolyBundleOn f i poly)

lemma omega_r_imp_poly (q r: ℝ) (hNonempty: (Set.Ioo q r).Nonempty) (hCInfinity: ContDiff ℝ ⊤ f): Set.Ioo q r ⊆ ⋃₀ {i | ∃ a b, i = Set.Ioo a b ∧ RestrictsToPoly f a b} → RestrictsToPolyOn f (Set.Ioo q r) := by
  intro s_subset_omega
  let all_intervals := {i | ∃ a b, i = Set.Ioo a b ∧ RestrictsToPoly f a b}
  let all_union := ⋃₀ all_intervals
  have all_open: ∀ s, s ∈ all_intervals → IsOpen (id s) := by
    intro s hs
    simp [all_intervals] at hs
    obtain ⟨a, b, hab, _⟩ := hs
    simp
    rw [hab]
    apply isOpen_Ioo


  have poly_on_closed: ∀ c d, c < d → Set.Icc c d ⊆ Set.Ioo q r →  RestrictsToPoly f c d := by
    intro c d c_lt_d cd_subset_s

    have cd_subset: Set.Icc c d ⊆ ⋃ i ∈ all_intervals, id i := by
      simp only [all_union, all_intervals]
      simp only [id]
      rw [← Set.sUnion_eq_biUnion]
      exact fun ⦃a⦄ a_1 ↦ s_subset_omega (cd_subset_s a_1)

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
      obtain ⟨i_in_fin, _⟩ := hi
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


  obtain ⟨c', d', c_lt_d', cd_int'⟩ := IsOpen.exists_Ioo_subset (isOpen_Ioo (a:= q) (b := r)) hNonempty
  let c := c' + (d' - c') / 4
  let d := d' - (d' - c') / 4
  have c_lt_d: c < d := by
    simp only [c, d]
    linarith
  have cd_subset_cd': Set.Icc c d ⊆ Set.Ioo c' d' := by
    simp only [c, d]
    intro x hx
    simp
    simp at hx
    refine ⟨?_, ?_⟩
    linarith
    linarith

  have cd_subset_s: Set.Icc c d ⊆ Set.Ioo q r := by
    exact fun ⦃a⦄ a_1 ↦ cd_int' (cd_subset_cd' a_1)

  obtain ⟨p_zero_one, h_p_zero_one⟩ := by apply poly_on_closed c d c_lt_d cd_subset_s
  use p_zero_one
  by_contra!
  simp [Function.ne_iff] at this
  obtain ⟨bad_x, h_bad_x⟩ := this

  -- Obtain an interval enclosing [0, 1] and having the bad point within (or an endpoint)
  let enclosing_open := Set.Ioo (min bad_x c) (max bad_x d)
  have min_lt_max: (min bad_x c) < (max bad_x d) := by
    simp
    right
    right
    exact c_lt_d

  have q_lt_c: q < c := by
    simp only [c]
    simp [Set.Ioo_subset_Ioo_iff c_lt_d'] at cd_int'
    linarith

  have d_lt_d: d < r := by
    simp only [d]
    simp [Set.Ioo_subset_Ioo_iff c_lt_d'] at cd_int'
    linarith

  obtain ⟨p_enclosing, h_p_enclosing⟩ := by
    apply poly_on_closed (min bad_x c) (max bad_x d) min_lt_max
    intro x hx
    simp
    refine ⟨?_, ?_⟩
    have x_gt_min: (min bad_x c) ≤ x := by
      simp at hx
      simp
      exact hx.1
    have q_lt_bad_x: q < bad_x := by
      exact h_bad_x.1.1
    have q_lt_min: q < min bad_x c := by
      apply lt_min q_lt_bad_x q_lt_c
    linarith

    have x_lt_max: x ≤ (max bad_x d) := by
      simp at hx
      simp
      exact hx.2

    have bad_x_lt_r: bad_x < r := by
      exact h_bad_x.1.2

    have max_lt_r: (max bad_x d) < r := by
      apply max_lt
      exact bad_x_lt_r
      exact d_lt_d
    linarith






  -- TODO - deduplicate this
  have intersect_infinite: (enclosing_open ∩ Set.Ioo c d).Infinite := by
    rw [Set.Ioo_inter_Ioo]
    apply Set.Ioo_infinite
    simp
    exact c_lt_d

  have diff_zero_all: (p_enclosing - p_zero_one) = 0 := by
    obtain ⟨nplusone_zeros, zeros_subset, zeros_card⟩ := @Set.Infinite.exists_subset_card_eq _ (enclosing_open ∩ Set.Ioo c d) intersect_infinite ((p_enclosing - p_zero_one).natDegree + 1)
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (p_enclosing - p_zero_one) nplusone_zeros
    intro y hy
    simp only [Set.subset_def] at zeros_subset
    have y_in_intersect: y ∈ enclosing_open ∩ Set.Ioo c d := by
      simp only [enclosing_open]
      have y_in_closed := zeros_subset y hy
      simp only [enclosing_open] at y_in_closed
      exact y_in_closed


    have eq_zero_intersect: ∀ z, z ∈ enclosing_open ∩ Set.Ioo c d → (p_enclosing - p_zero_one).eval z = 0 := by
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
  linarith
  exact hCInfinity



lemma poly_overlap_implies_eq (f: ℝ → ℝ) (s_p s_q: Set ℝ) (p q: Polynomial ℝ) (hp: RestrictsToPolyBundleOn f s_p p) (hq: RestrictsToPolyBundleOn f s_q q) (hInteresct: (s_p ∩ s_q).Infinite) : p = q := by
  have diff_zero_all: (p - q) = 0 := by
    obtain ⟨nplusone_zeros, zeros_subset, zeros_card⟩ := @Set.Infinite.exists_subset_card_eq _ (s_p ∩ s_q) hInteresct ((p - q).natDegree + 1)
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (p - q) nplusone_zeros
    intro y hy
    simp only [Set.subset_def] at zeros_subset
    have y_in_intersect: y ∈ (s_p ∩ s_q) := zeros_subset y hy
    have eq_zero_intersect: ∀ z, z ∈ (s_p ∩ s_q) → (p - q).eval z = 0 := by
      intro z ⟨hz1, hz2⟩
      simp
      rw [← hp z hz1]
      rw [← hq z hz2]
      simp

    apply eq_zero_intersect
    apply y_in_intersect
    rw [zeros_card]
    simp

  apply eq_of_sub_eq_zero diff_zero_all

-- https://mathoverflow.net/questions/34059/if-f-is-infinitely-differentiable-then-f-coincides-with-a-polynomial
theorem infinite_zero_is_poly (hf: ∀ (x : ℝ), ∃ (n: ℕ), (iteratedDeriv n f) x = 0) (hCInfinity: ContDiff ℝ ⊤ f): RestrictsToPoly f 0 1 := by
  -- let real_powset := 𝒫 { z: ℝ | True }
  let poly_omega := Set.sUnion { i | ∃ (a b : ℝ ), i = Set.Ioo a b ∧ RestrictsToPoly f a b }
  have poly_open: IsOpen poly_omega := by
    apply isOpen_sUnion
    intro t ht
    simp at ht
    obtain ⟨a, b, h, _⟩ := ht
    rw [h]
    apply isOpen_Ioo


  let e_n := fun k => { x: ℝ | (iteratedDeriv k f) x = 0 }

  -- LEAN BUG - try moving this into a 'have' block that already contains errors
  have r_closed: OrderClosedTopology ℝ := by
    apply NormedLatticeAddCommGroup.orderClosedTopology
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

      have gx_nonempty: Set.Nonempty (Set.Ioo g x) := by
        apply Set.nonempty_Ioo.mpr g_lt_x

      have hx_nonempty: Set.Nonempty (Set.Ioo x h) := by
        apply Set.nonempty_Ioo.mpr x_lt_h


      have is_first_poly_on: RestrictsToPolyOn f (Set.Ioo g x) := by
        apply omega_r_imp_poly g x gx_nonempty
        exact hCInfinity
        simp only [poly_omega] at left_subset_omega
        apply left_subset_omega

      have is_second_poly_on: RestrictsToPolyOn f (Set.Ioo x h) := by
        apply omega_r_imp_poly x h hx_nonempty
        exact hCInfinity
        simp only [poly_omega] at right_subset_omega
        apply right_subset_omega

      have is_first_poly: RestrictsToPoly f g x := is_first_poly_on
      have is_second_poly: RestrictsToPoly f x h := is_second_poly_on

      obtain ⟨first_poly, h_first_poly⟩ := is_first_poly
      obtain ⟨second_poly, h_second_poly⟩ := is_second_poly

      let n := max first_poly.natDegree second_poly.natDegree
      have zero_on_new: ∀ (y: ℝ), y ∈ (Set.Ioo g h) → (iteratedDeriv (n + 1) f) y = 0 := by
        have orig_first_degree_zero: ((⇑Polynomial.derivative)^[n] first_poly).natDegree ≤ first_poly.natDegree - n := by
          apply Polynomial.natDegree_iterate_derivative first_poly n
        simp at orig_first_degree_zero


        -- FIXME - remove copy-paste with 'orig_first_degree_zero' code above
        have orig_second_degree_zero: ((⇑Polynomial.derivative)^[n] second_poly).natDegree ≤ second_poly.natDegree - n := by
          apply Polynomial.natDegree_iterate_derivative second_poly n
        simp at orig_second_degree_zero

        have f_deriv_zero: ∀ (y: ℝ), y ∈ (Set.Ioo g x ∪ Set.Ioo x h) → (iteratedDeriv (n + 1) f) y = 0 := by
          intro y hy
          rw [Set.mem_union] at hy
          cases hy with
          | inl y_in_left =>
            have derivwith_eq: Set.EqOn (iteratedDerivWithin (n + 1) f (Set.Ioo g x)) (iteratedDerivWithin (n + 1) first_poly.eval (Set.Ioo g x)) (Set.Ioo g x) := by
              apply iteratedDerivWithin_congr
              apply uniqueDiffOn_Ioo
              apply h_first_poly


            rw [Set.EqOn] at derivwith_eq
            specialize derivwith_eq y_in_left
            nth_rewrite 2 [iteratedDerivWithin] at derivwith_eq
            rw [iteratedFDerivWithin_of_isOpen (n + 1) (isOpen_Ioo) y_in_left] at derivwith_eq
            rw [← iteratedDeriv] at derivwith_eq
            rw [poly_iterated_deriv (n + 1)] at derivwith_eq
            rw [Polynomial.iterate_derivative_eq_zero] at derivwith_eq
            simp at derivwith_eq
            rw [iteratedDerivWithin] at derivwith_eq
            rw [iteratedFDerivWithin_of_isOpen (n + 1) (isOpen_Ioo) y_in_left] at derivwith_eq
            rw [← iteratedDeriv] at derivwith_eq
            exact derivwith_eq
            simp only [n]
            have le_max: first_poly.natDegree ≤ max first_poly.natDegree second_poly.natDegree := by
              simp
            rw [← Nat.lt_add_one_iff] at le_max
            exact le_max
          | inr y_in_right =>
            -- FIXME - deduplicate this with the left-hand proof
            have derivwith_eq: Set.EqOn (iteratedDerivWithin (n + 1) f (Set.Ioo x h)) (iteratedDerivWithin (n + 1) second_poly.eval (Set.Ioo x h)) (Set.Ioo x h) := by
              apply iteratedDerivWithin_congr
              apply uniqueDiffOn_Ioo
              apply h_second_poly


            rw [Set.EqOn] at derivwith_eq
            specialize derivwith_eq y_in_right
            nth_rewrite 2 [iteratedDerivWithin] at derivwith_eq
            rw [iteratedFDerivWithin_of_isOpen (n + 1) (isOpen_Ioo) y_in_right] at derivwith_eq
            rw [← iteratedDeriv] at derivwith_eq
            rw [poly_iterated_deriv (n + 1)] at derivwith_eq
            rw [Polynomial.iterate_derivative_eq_zero] at derivwith_eq
            simp at derivwith_eq
            rw [iteratedDerivWithin] at derivwith_eq
            rw [iteratedFDerivWithin_of_isOpen (n + 1) (isOpen_Ioo) y_in_right] at derivwith_eq
            rw [← iteratedDeriv] at derivwith_eq
            exact derivwith_eq
            simp only [n]
            have le_max: second_poly.natDegree ≤ max first_poly.natDegree second_poly.natDegree := by
              simp
            rw [← Nat.lt_add_one_iff] at le_max
            exact le_max

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
        have f_zero_full: ∀ (y: ℝ), y ∈ (Set.Ioo g h) → (iteratedDeriv (n + 1) f) y = 0 := by
          intro y hy
          simp at hy
          have y_cases: y = x ∨ y ≠ x := by
            apply eq_or_ne y x
          cases y_cases with
          | inl y_eq_x =>
            rw [y_eq_x]
            exact f_deriv_at_x
          | inr y_neq_x =>
            have y_in_union: y ∈ (Set.Ioo g x ∪ Set.Ioo x h) := by
              have y_lt_or_gt: y < x ∨ x < y := by
                apply lt_or_gt_of_ne y_neq_x
              cases y_lt_or_gt with
              | inl y_lt_x =>
                rw [Set.mem_union]
                left
                simp
                refine ⟨?_, ?_⟩
                linarith
                linarith
              | inr x_lt_y =>
                rw [Set.mem_union]
                right
                simp
                refine ⟨?_, ?_⟩
                linarith
                linarith
            apply f_deriv_zero y y_in_union
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

    let x_subspace :=  { x: ℝ // x ∈ X }

    have x_subspace_enk_eq : ∀ k: ℕ, ({x : x_subspace | x.1 ∈ (e_n k)}) = X ∩ e_n k := by
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

    have en_closed_subtype_x: ∀ k: ℕ, IsClosed ({x : X | x.1 ∈ e_n k}) := by
      intro k
      specialize x_subspace_enk_eq k
      simp only [e_n]
      simp
      apply isClosed_eq
      refine Continuous.comp' ?_ ?_
      apply ContDiff.continuous_iteratedDeriv k hCInfinity
      simp
      exact continuous_subtype_val
      exact continuous_const


    have x_intersect_closed: ∀ k: ℕ , IsClosed (X := x_subspace) (Set.univ ∩ {x: X | x.1 ∈ e_n k }) := by
      intro k
      apply IsClosed.inter
      apply isClosed_univ
      apply en_closed_subtype_x k


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


    have en_cov_univ_set_x: (@Set.univ x_subspace) = Set.iUnion fun j => Set.univ ∩ ({x: x_subspace | x.1 ∈ e_n j}) := by
      ext p
      obtain ⟨n, hn⟩ := hf p
      have p_in_en: p.1 ∈ (e_n n) := by
        simp only [e_n]
        simp
        exact hn

      constructor
      -- first case
      intro p_in_univ
      have p_in_intersect: p.1 ∈ (e_n n) ∩ Set.univ := by
        apply Set.mem_inter
        exact p_in_en
        exact p_in_univ

      simp only [Set.mem_iUnion]
      use n
      obtain ⟨real_p, hp⟩ := p
      simp
      exact p_in_en

      simp

    have x_set_complete: IsComplete X := by
      apply IsClosed.isComplete
      exact X_closed

    have complete_space: CompleteSpace x_subspace := by
      apply IsComplete.completeSpace_coe
      exact x_set_complete

    by_contra!

    have subspace_nonempty: Nonempty x_subspace := by
      exact Set.Nonempty.to_subtype this

    rw [eq_comm] at x_union_en
    -- Apply baire category theorem again.
    obtain ⟨n_x_int, x_int_nonempty⟩ := nonempty_interior_of_iUnion_of_closed x_intersect_closed en_cov_univ_set_x.symm
    have x_int_open: IsOpen (interior (@Set.univ x_subspace ∩ {x | ↑x ∈ e_n n_x_int})) := by apply isOpen_interior


    have x_int_open_copy := x_int_open
    simp only [IsOpen] at x_int_open
    rw [TopologicalSpace.IsOpen] at x_int_open
    simp [instTopologicalSpaceSubtype, TopologicalSpace.induced] at x_int_open
    -- An open set in the topology on R
    obtain ⟨full_set, full_set_open, full_set_preimage⟩ := x_int_open
    rw [Set.preimage] at full_set_preimage

    have full_set_preimage_reverse: interior {x: x_subspace | ↑x ∈ e_n n_x_int} = (Subtype.val ⁻¹' full_set) := full_set_preimage.symm
    rw [Set.eq_preimage_subtype_val_iff] at full_set_preimage_reverse

    have x_int_nonempty_copy := x_int_nonempty
    obtain ⟨some_x, h_some_x⟩ := x_int_nonempty_copy
    have some_x_in_full: some_x.1 ∈ full_set := by
      simp at h_some_x
      apply (full_set_preimage_reverse some_x.1 some_x.2).mp h_some_x

    have full_set_is_neighborhood := IsOpen.mem_nhds full_set_open some_x_in_full
    obtain ⟨c, d, some_in_cd, cd_subset_full_temp⟩ := mem_nhds_iff_exists_Ioo_subset.mp full_set_is_neighborhood

    have cd_int: Set.Ioo c d ∩ X ⊆ X ∩ (e_n n_x_int) := by
      rw [Set.subset_def]
      intro x hx
      specialize full_set_preimage_reverse x hx.2
      have x_in_full: x ∈ full_set := cd_subset_full_temp hx.1
      have x_in_interior := full_set_preimage_reverse.mpr x_in_full
      have x_in_en := Set.mem_of_mem_of_subset x_in_interior interior_subset
      simp at x_in_en
      apply Set.mem_inter hx.2 x_in_en

    let cd_intersect_x := Set.Ioo c d ∩ X

    have cd_intersect_x_nonempty: cd_intersect_x.Nonempty := by
      simp only [cd_intersect_x]
      rw [Set.nonempty_def]
      use some_x.1
      refine ⟨some_in_cd, some_x.2⟩

    have cd_nonempty: (Set.Ioo c d).Nonempty := Set.Nonempty.left cd_intersect_x_nonempty
    have c_lt_d: c < d := Set.nonempty_Ioo.mp cd_nonempty



    have x_zero_on_cd_intersect: ∀ (x: ℝ), x ∈ cd_intersect_x → (iteratedDeriv n_x_int f) x = 0 := by
      rw [Set.subset_def] at cd_int
      intro x hx
      specialize cd_int x hx
      simp only [e_n] at cd_int
      apply cd_int.2

    have n_succ_deriv_zero: ∀ (x: ℝ) (k: ℕ), x ∈ cd_intersect_x → (∀ y, y ∈ cd_intersect_x → (iteratedDeriv (k) f) y = 0) → (iteratedDeriv (k + 1) f) x = 0 := by
      intro x k hx deriv_x_zero
      rw [iteratedDeriv_succ]

      have cont_diff_within_at: ContDiffWithinAt ℝ ⊤ (deriv (iteratedDeriv k f)) (Set.Ioo c d) x:= by
        rw [← iteratedDeriv_succ]
        have iterate_deriv_cont := by apply ContDiff.iterate_deriv (k + 1) hCInfinity
        simp only [← iteratedDeriv_eq_iterate] at iterate_deriv_cont
        apply ContDiff.contDiffWithinAt iterate_deriv_cont

      have deriv_tendsto_at_x: Filter.Tendsto (deriv (iteratedDeriv k f)) (nhdsWithin x (Set.Ioo c d)) (nhds ((deriv (iteratedDeriv k f)) x)) := by
        apply ContinuousWithinAt.tendsto _
        apply ContDiffWithinAt.continuousWithinAt cont_diff_within_at

      have x_accum_cd_inter: ∀ x, x ∈ cd_intersect_x → AccPt x (Filter.principal cd_intersect_x) := by
        intro x hx
        have x_acc_x: AccPt x (Filter.principal X) := x_accum x hx.2
        rw [accPt_iff_frequently] at x_acc_x
        rw [accPt_iff_frequently]
        rw [Filter.frequently_iff] at x_acc_x
        rw [Filter.frequently_iff]
        intro u hu
        have x_in_cd: x ∈ Set.Ioo c d := by
          apply hx.1
        have cd_nhds: Set.Ioo c d ∈ 𝓝 x := Ioo_mem_nhds x_in_cd.1 x_in_cd.2
        have intersect_neighbor: u ∩ Set.Ioo c d ∈ 𝓝 x := by
          apply Filter.inter_mem hu cd_nhds

        specialize x_acc_x intersect_neighbor
        obtain ⟨x1, x1_in_inter, x1_neq_x, x1_in_x⟩ := x_acc_x
        use x1
        refine ⟨x1_in_inter.1, x1_neq_x, ?_⟩
        simp only [cd_intersect_x]
        exact ⟨x1_in_inter.2, x1_in_x⟩


      apply Filter.tendsto_iff_seq_tendsto.mp at deriv_tendsto_at_x
      have x_acc: AccPt x (Filter.principal cd_intersect_x) := x_accum_cd_inter x hx
      rw [accPt_iff_frequently] at x_acc
      rw [Filter.frequently_iff_seq_forall] at x_acc
      obtain ⟨x_seq, x_seq_tendsto, x_seq_in_X⟩ := x_acc
      have deriv_x_seq_zero: ∀ n, (iteratedDeriv k f) (x_seq n) = 0 := by
        intro n
        specialize x_seq_in_X n
        apply deriv_x_zero (x_seq n) x_seq_in_X.2

      have cont_iterated: ContDiff ℝ ⊤ (deriv^[k] f) := ContDiff.iterate_deriv k hCInfinity
      rw [← iteratedDeriv_eq_iterate] at cont_iterated

      have has_strict_deriv_at_x: HasStrictDerivAt (iteratedDeriv k f) (deriv ((iteratedDeriv k f)) x) x := by
        apply ContDiff.hasStrictDerivAt cont_iterated
        simp
      have has_deriv_at_x: HasDerivAt (iteratedDeriv k f) (deriv ((iteratedDeriv k f)) x) x := by
        apply HasStrictDerivAt.hasDerivAt (has_strict_deriv_at_x)

      have slope_tendsto: Tendsto (slope (iteratedDeriv k f) x) (𝓝[≠] x) (𝓝 (deriv (iteratedDeriv k f) x)) := by
        rw [hasDerivAt_iff_tendsto_slope] at has_deriv_at_x
        exact has_deriv_at_x

      apply Filter.tendsto_iff_seq_tendsto.mp at slope_tendsto

      have slope_zero_on_seq: ∀ n, (slope ((iteratedDeriv k f)) x (x_seq n)) = 0 := by
        intro n
        rw [slope]
        rw [deriv_x_seq_zero n]
        rw [deriv_x_zero x hx]
        simp

      have slope_zero_comp: slope (iteratedDeriv k f) x ∘ x_seq = 0 := by
        ext n
        simp
        apply slope_zero_on_seq n

      have slope_zero_tendsto: Tendsto x_seq atTop (𝓝[≠] x) →
          Tendsto (slope (iteratedDeriv k f) x ∘ x_seq) atTop (𝓝 (deriv (iteratedDeriv k f) x)) := by
        exact fun a ↦ slope_tendsto x_seq a

      have x_seq_tendsto_x: Tendsto x_seq atTop (𝓝[≠] x) := by
        rw [Tendsto]
        rw [Filter.le_def]
        rw [Tendsto] at x_seq_tendsto
        rw [Filter.le_def] at x_seq_tendsto
        simp
        simp at x_seq_tendsto
        intro x_1 hx_1
        let x1_with_x := x_1 ∪ {x}
        have x1_with_x_in_nhds: x1_with_x ∈ 𝓝 x := by
          rw [mem_nhds_iff]
          rw [mem_nhdsWithin] at hx_1
          obtain ⟨u, hu⟩ := hx_1
          use u
          refine ⟨?_, hu.1, ?_⟩
          simp only [x1_with_x]
          rw [Set.subset_def]
          intro y hy
          have y_cases: y = x ∨ y ≠ x := by
            apply eq_or_ne y x
          cases y_cases with
          | inl y_eq_x =>
            rw [y_eq_x]
            exact Set.mem_union_right x_1 rfl
          | inr y_neq_x =>
            have y_in_inter: y ∈ u ∩ {x}ᶜ := by
              exact Set.mem_inter hy y_neq_x
            have y_in_x1: y ∈ x_1 := by
              apply hu.2.2 y_in_inter
            apply Set.mem_union_left (x := y)
            exact y_in_x1
          exact hu.2.1
        obtain ⟨a, ha⟩ := x_seq_tendsto x1_with_x x1_with_x_in_nhds
        use a
        intro b hb
        specialize ha b hb
        specialize x_seq_in_X b
        simp only [x1_with_x] at ha
        simp only [x_seq_in_X.1] at ha
        simp [x_seq_in_X.1] at ha
        exact ha

      specialize slope_zero_tendsto x_seq_tendsto_x
      rw [slope_zero_comp] at slope_zero_tendsto

      -- TODO - figure out how this actually works - not sure why this compiles.
      have tendsto_zero := by apply tendsto_nhds_unique (slope_zero_tendsto) tendsto_const_nhds
      apply tendsto_zero


    have zero_forall_m: ∀ m, ∀ x, m ≥ n_x_int →  x ∈ cd_intersect_x → (iteratedDeriv m f) x = 0 := by
      intro m x hm hx
      induction m, hm using Nat.le_induction generalizing x with
      | base => exact x_zero_on_cd_intersect x hx
      | succ k _ hx_new =>
        apply n_succ_deriv_zero x k hx
        exact hx_new


    -- "We will prove that f(n)=0 on (a,b). This will imply that (a,b)⊂Ω which is a contradiction with (3)."
    have deriv_zero_on_cd_int_omega: ∀ (x : ℝ), x ∈ (Set.Ioo c d) ∩ poly_omega → (iteratedDeriv n_x_int f) x = 0 := by
      intro x hx
      have int_open: IsOpen ((Set.Ioo c d) ∩ poly_omega) := by
        apply IsOpen.inter
        apply isOpen_Ioo
        apply poly_open
      have is_empty_or_nonempty: (Set.Ioo c d ∩ poly_omega).Nonempty ∨ (Set.Ioo c d ∩ poly_omega) = ∅ := by
        exact Or.symm (Set.eq_empty_or_nonempty (Set.Ioo c d ∩ poly_omega))
      cases is_empty_or_nonempty with
      | inl inter_nonempty =>

        let maximal_set := ⋃₀ {i | ∃ a b, i = Set.Ioo a b ∧ RestrictsToPoly f a b ∧ x ∈ i ∧ i ⊆ Set.Ioo c d }
        have maximal_open: IsOpen maximal_set := by
          refine isOpen_sUnion ?_
          intro t ht
          simp only [Set.mem_setOf_eq] at ht
          obtain ⟨a, b, t_eq, _⟩ := ht
          rw [t_eq]
          apply isOpen_Ioo
        have x_in_maximal: x ∈ maximal_set := by
          have x_in_poly: x ∈ poly_omega := hx.2
          rw [Set.mem_sUnion] at x_in_poly
          obtain ⟨t, ht, x_in_t⟩ := x_in_poly
          simp only [Set.mem_setOf_eq] at ht
          obtain ⟨a, b, h_t, h_ab⟩ := ht
          have restricts_new: RestrictsToPoly f (max a c) (min b d) := by
            rw [RestrictsToPoly]
            obtain ⟨p, hp⟩ := h_ab
            use p
            intro y hy
            have y_in_ab: y ∈ Set.Ioo a b := by
              simp
              simp at hy
              refine ⟨?_, ?_⟩
              linarith
              linarith
            apply hp y y_in_ab
          have x_in_new: x ∈ Set.Ioo (max a c) (min b d) := by
            refine ⟨?_, ?_⟩
            rw [h_t] at x_in_t
            simp at x_in_t
            simp at hx
            simp
            refine ⟨x_in_t.1, hx.1.1⟩
            rw [h_t] at x_in_t
            simp at x_in_t
            simp
            refine ⟨x_in_t.2, ?_⟩
            apply hx.1.2

          have new_nonempty: Set.Nonempty (Set.Ioo (max a c) (min b d)) := by
            exact Set.nonempty_of_mem x_in_new

          have new_subset:  Set.Ioo (max a c) (min b d) ⊆ Set.Ioo c d := by
            rw [Set.Ioo_subset_Ioo_iff]
            refine ⟨?_, ?_⟩
            simp
            simp
            apply Set.nonempty_Ioo.mp new_nonempty


          use Set.Ioo (max a c) (min b d)
          simp only [Set.mem_setOf_eq]
          refine ⟨?_, x_in_new⟩
          refine ⟨(max a c), (min b d), rfl, restricts_new, x_in_new, new_subset⟩
        have maximal_nonempty: maximal_set.Nonempty := by
          exact Set.nonempty_of_mem x_in_maximal

        have maximal_is_connected: IsConnected maximal_set := by
          refine ⟨maximal_nonempty, ?_⟩
          apply isPreconnected_sUnion x
          intro s hs
          simp only [Set.mem_setOf_eq] at hs
          obtain ⟨a, b, _, _, x_in_s, _⟩ := hs
          exact x_in_s
          intro s hs
          obtain ⟨a, b, h_s, _⟩ := hs
          rw [h_s]
          apply isPreconnected_Ioo

        have maximal_mem_intervals := IsPreconnected.mem_intervals maximal_is_connected.2
        have sets_subset: {i | ∃ a b, i = Set.Ioo a b ∧ RestrictsToPoly f a b ∧ x ∈ i ∧ i ⊆ Set.Ioo c d} ⊆ {i | ∃ a b, i = Set.Ioo a b ∧ RestrictsToPoly f a b} := by
          simp
          intro a x_2 x_3 h_a_eq h_poly _ _
          use x_2
          use x_3

        have maximal_neq_not_open: ∀s, ¬ IsOpen s → ¬(maximal_set = s) := by
          intro s hs
          by_contra!
          rw [this] at maximal_open
          contradiction

        have maximal_subset_cd: maximal_set ⊆ Set.Ioo c d := by
          simp only [maximal_set]
          rw [Set.sUnion_subset_iff]
          intro t ht
          simp only [Set.mem_setOf_eq] at ht
          obtain ⟨_, _, _, _, _, t_subset⟩ := ht
          exact t_subset

        have maximal_bounded_above: BddAbove maximal_set := by
          rw [bddAbove_def]
          use d
          simp at maximal_subset_cd
          intro y hy
          specialize maximal_subset_cd hy
          simp at maximal_subset_cd
          exact le_of_lt maximal_subset_cd.2

        have maximal_bounded_below: BddBelow maximal_set := by
          rw [bddBelow_def]
          use c
          simp at maximal_subset_cd
          intro y hy
          specialize maximal_subset_cd hy
          simp at maximal_subset_cd
          exact le_of_lt maximal_subset_cd.1

        have maximal_neq_unbounded_below: ∀s, ¬ BddBelow s → ¬(maximal_set = s) := by
          intro s hs
          by_contra!
          rw [this] at maximal_bounded_below
          contradiction

        have maximal_neq_unbounded_above: ∀s, ¬ BddAbove s → ¬(maximal_set = s) := by
          intro s hs
          by_contra!
          rw [this] at maximal_bounded_above
          contradiction

        obtain ⟨a, b, a_lt_b, ab_subset⟩ := IsOpen.exists_Ioo_subset maximal_open maximal_nonempty

        have glb_ab: IsGLB (Set.Ioo a b) a := isGLB_Ioo a_lt_b
        have lub_ab: IsLUB (Set.Ioo a b) b := isLUB_Ioo a_lt_b

        have inf_le_sup: (sInf maximal_set) ≤  (sSup maximal_set) := by
          apply Real.sInf_le_sSup maximal_set maximal_bounded_below maximal_bounded_above


        have inf_glb: IsGLB maximal_set (sInf maximal_set) := Real.is_glb_sInf maximal_set maximal_nonempty maximal_bounded_below
        have sup_lub: IsLUB maximal_set (sSup maximal_set) := Real.isLUB_sSup maximal_set maximal_nonempty maximal_bounded_above

        have glb_subset: (sInf maximal_set) ≤ a := by
          apply IsGLB.mono glb_ab inf_glb ab_subset

        have lub_subset: b ≤ (sSup maximal_set) := by
          apply IsLUB.mono lub_ab sup_lub ab_subset

        have inf_lt_sup: (sInf maximal_set) < (sSup maximal_set) := by
          calc
            sInf maximal_set ≤ a := glb_subset
            _ < b := a_lt_b
            _ ≤ sSup (maximal_set) := lub_subset


        have maximal_is_interval: ∃ p q, maximal_set = Set.Ioo p q := by
          have neq_icc := maximal_neq_not_open (Set.Icc (sInf maximal_set) (sSup maximal_set)) (icc_not_open _ _ inf_le_sup)
          have neq_ici := maximal_neq_not_open (Set.Ici (sInf maximal_set)) (ici_not_open _)
          have neq_iic := maximal_neq_not_open (Set.Iic (sSup maximal_set)) (iic_not_open _)
          have neq_ico := maximal_neq_not_open (Set.Ico (sInf maximal_set) (sSup maximal_set)) (ico_not_open _ _ inf_lt_sup)
          have neq_ioc := maximal_neq_not_open (Set.Ioc (sInf maximal_set) (sSup maximal_set)) (ioc_not_open _ _ inf_lt_sup)
          have neq_ioi := maximal_neq_unbounded_above (Set.Ioi (sInf maximal_set)) (not_bddAbove_Ioi _)
          have neq_iio := maximal_neq_unbounded_below (Set.Iio (sSup maximal_set)) (not_bddBelow_Iio _)
          have neq_univ := maximal_neq_unbounded_above Set.univ (not_bddAbove_univ)
          simp [Set.mem_insert_iff] at maximal_mem_intervals
          simp only [neq_icc, neq_ici, neq_iic, neq_ico, neq_ioc, neq_ioi, neq_iio, Set.Nonempty.ne_empty maximal_nonempty, neq_univ] at maximal_mem_intervals
          simp at maximal_mem_intervals
          refine ⟨(sInf maximal_set), (sSup maximal_set), maximal_mem_intervals⟩



        obtain ⟨p, q, maximal_set_eq⟩ := maximal_is_interval
        have x_in_pq: x ∈ Set.Ioo p q := by
          rw [← maximal_set_eq]
          exact x_in_maximal
        have p_lt_q: p < q := by
          rw [maximal_set_eq] at maximal_nonempty
          exact Set.nonempty_Ioo.mp maximal_nonempty

        have pq_poly_on: RestrictsToPolyOn f (Set.Ioo p q) := by
          apply omega_r_imp_poly p q (Set.nonempty_Ioo.mpr p_lt_q)
          exact hCInfinity
          simp only [← maximal_set_eq, maximal_set]
          rw [Set.subset_def]
          intro x1 hx1
          simp only [Set.mem_sUnion] at hx1
          simp only [Set.mem_sUnion]
          obtain ⟨t, ht, x_in_t⟩ := hx1
          use t
          refine ⟨?_, x_in_t⟩
          apply sets_subset ht



        have pq_not_cd: p ≠ c ∨ q ≠ d := by
          by_contra!
          obtain ⟨z, hz⟩ := cd_intersect_x_nonempty
          have z_in_x: z ∈ X := by
            exact hz.2
          have z_in_maximal: z ∈ maximal_set := by
            rw [maximal_set_eq]
            simp only [cd_intersect_x] at hz
            rw [this.1, this.2]
            exact hz.1
          have z_in_poly_omega: z ∈ poly_omega := by
            simp only [poly_omega]
            rw [Set.mem_sUnion]
            obtain ⟨t, ht, z_in_t⟩ := z_in_maximal
            use t
            refine ⟨sets_subset ht, z_in_t⟩

          simp only [X] at z_in_x
          contradiction

        have pq_subset_cd: Set.Ioo p q ⊆ Set.Ioo c d := by
          rw [Set.subset_def]
          intro y hy
          rw [← maximal_set_eq] at hy
          simp only [maximal_set, Set.mem_sUnion] at hy
          obtain ⟨t, t_in, y_in_t⟩ := hy
          simp only [Set.mem_setOf_eq] at t_in
          obtain ⟨a, b, _, _, _, t_subset⟩ := t_in
          apply t_subset y_in_t

        have p_or_q_in_cd: p ∈ Set.Ioo c d ∨ q ∈ Set.Ioo c d := by
          rw [Set.Ioo_subset_Ioo_iff p_lt_q] at pq_subset_cd
          cases pq_not_cd with
          | inl p_not_c =>
            rw [le_iff_eq_or_lt] at pq_subset_cd
            have p_not_c := p_not_c.symm
            simp at p_not_c
            simp [p_not_c] at pq_subset_cd
            left
            simp
            refine ⟨?_, ?_⟩
            linarith
            linarith
          | inr q_not_d =>
            nth_rewrite 2 [le_iff_eq_or_lt] at pq_subset_cd
            simp at q_not_d
            simp [q_not_d] at pq_subset_cd
            right
            simp
            refine ⟨?_, ?_⟩
            linarith
            linarith


        have p_or_q_in: p ∈ cd_intersect_x ∨ q ∈ cd_intersect_x := by
          by_contra!
          simp only [cd_intersect_x, X, poly_omega] at this

          cases p_or_q_in_cd with
          | inl p_in_cd =>
            have p_not_inter: ¬ (p ∈ _) := this.1
            simp only [Set.mem_inter_iff] at p_not_inter
            rw [not_and_or] at p_not_inter
            simp only [p_in_cd] at p_not_inter
            simp at p_not_inter
            obtain ⟨p_set, a_p, b_p, p_set_eq, p_restricts, p_in_Ioo⟩ := p_not_inter
            simp [p_set_eq] at p_in_Ioo
            let new_set := Set.Ioo (max a_p c) q

            have x_in_new: x ∈ new_set := by
              refine ⟨?_, ?_⟩
              simp
              simp at x_in_pq
              refine ⟨?_, ?_⟩
              linarith
              simp at p_in_cd
              linarith
              simp at x_in_pq
              linarith

            rw [RestrictsToPolyOn] at pq_poly_on
            obtain ⟨full_poly, h_full_poly⟩ := pq_poly_on

            obtain ⟨p_poly, hp_poly⟩ := p_restricts

            have new_restricts: RestrictsToPolyBundleOn f (Set.Ioo (max a_p c) (min b_p d)) p_poly := by
              simp only [RestrictsToPolyBundleOn]
              intro y hy
              have y_in_set: y ∈ Set.Ioo a_p b_p := by
                rw [Set.mem_Ioo]
                simp at hy
                refine ⟨?_, ?_⟩
                linarith
                linarith


              specialize hp_poly y y_in_set
              exact hp_poly

            have c_lt_p: c < p := by
              simp at p_in_cd
              linarith

            have p_lt_d: p < d := by
              simp at p_in_cd
              linarith

            have intersect_infinite: ((Set.Ioo (max a_p c) (min b_p d)) ∩ Set.Ioo p q).Infinite := by
              rw [Set.Ioo_inter_Ioo]
              apply Set.Ioo_infinite
              simp
              refine ⟨?_, ?_⟩
              refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
              refine ⟨?_, ?_⟩
              linarith
              linarith
              linarith
              linarith
              linarith
              linarith
              refine ⟨⟨?_, ?_⟩, ?_⟩
              linarith
              linarith
              linarith






            have polys_eq := poly_overlap_implies_eq f (Set.Ioo (max a_p c) (min b_p d)) (Set.Ioo p q) p_poly full_poly new_restricts h_full_poly intersect_infinite
            have p_in_maximal: p ∈ maximal_set := by
              simp only [maximal_set]
              rw [Set.mem_sUnion]
              use new_set
              refine ⟨?_, ?_⟩
              simp only [Set.mem_setOf_eq]
              use (max a_p c)
              use q
              refine ⟨rfl, ?_, ?_⟩
              rw [RestrictsToPolyBundleOn] at new_restricts
              rw [RestrictsToPoly]
              use full_poly
              intro y hy
              simp at hy
              have y_cases_b_p: y < b_p ∨ y ≥ b_p := lt_or_ge _ _


              cases y_cases_b_p with
              | inl y_lt_bp =>
                have y_in_set: y ∈ Set.Ioo a_p b_p := by
                  rw [Set.mem_Ioo]
                  refine ⟨?_, ?_⟩
                  linarith
                  linarith
                specialize hp_poly y y_in_set
                rw [polys_eq] at hp_poly
                exact hp_poly

              | inr y_ge_bp =>
                have y_in_set: y ∈ Set.Ioo p q := by
                  rw [Set.mem_Ioo]
                  refine ⟨?_, ?_⟩
                  linarith
                  linarith
                specialize h_full_poly y y_in_set
                exact h_full_poly

              refine ⟨x_in_new, ?_⟩
              simp only [new_set]
              rw [Set.Ioo_subset_Ioo_iff]
              refine ⟨?_, ?_⟩
              simp
              rw [Set.Ioo_subset_Ioo_iff] at pq_subset_cd
              linarith
              linarith
              simp
              refine ⟨?_, ?_⟩
              linarith
              linarith
              simp [new_set]
              refine ⟨⟨?_, ?_⟩, ?_⟩
              linarith
              linarith
              linarith







            rw [maximal_set_eq] at p_in_maximal
            simp at p_in_maximal
          | inr q_in_cd =>
          -- BEGIN HORRIBLE COPY-PASTE --
            have q_not_inter: ¬ (q ∈ _) := this.2
            simp only [Set.mem_inter_iff] at q_not_inter
            rw [not_and_or] at q_not_inter
            simp only [q_in_cd] at q_not_inter
            simp at q_not_inter
            obtain ⟨q_set, a_q, b_q, q_set_eq, q_restricts, q_in_Ioo⟩ := q_not_inter
            simp [q_set_eq] at q_in_Ioo
            let new_set := Set.Ioo p (min b_q d)

            have x_in_new: x ∈ new_set := by
              refine ⟨?_, ?_⟩
              simp at x_in_pq
              linarith
              simp
              refine ⟨?_, ?_⟩
              simp at q_in_cd
              simp at x_in_pq
              linarith
              simp at x_in_pq
              simp at q_in_cd
              linarith

            rw [RestrictsToPolyOn] at pq_poly_on
            obtain ⟨full_poly, h_full_poly⟩ := pq_poly_on

            obtain ⟨q_poly, hq_poly⟩ := q_restricts

            have new_restricts: RestrictsToPolyBundleOn f (Set.Ioo (max a_q c) (min b_q d)) q_poly := by
              simp only [RestrictsToPolyBundleOn]
              intro y hy
              have y_in_set: y ∈ Set.Ioo a_q b_q := by
                rw [Set.mem_Ioo]
                simp at hy
                refine ⟨?_, ?_⟩
                linarith
                linarith


              specialize hq_poly y y_in_set
              exact hq_poly

            have c_lt_q: c < q := by
              simp at q_in_cd
              linarith

            have q_lt_d: q < d := by
              simp at q_in_cd
              linarith

            have intersect_infinite: ((Set.Ioo (max a_q c) (min b_q d)) ∩ Set.Ioo p q).Infinite := by
              rw [Set.Ioo_inter_Ioo]
              apply Set.Ioo_infinite
              simp
              refine ⟨?_, ?_⟩
              refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
              refine ⟨?_, ?_⟩
              linarith
              linarith
              linarith
              linarith
              linarith
              linarith
              refine ⟨⟨?_, ?_⟩, ?_⟩
              linarith
              linarith
              linarith






            have polys_eq := poly_overlap_implies_eq f (Set.Ioo (max a_q c) (min b_q d)) (Set.Ioo p q) q_poly full_poly new_restricts h_full_poly intersect_infinite
            have q_in_maximal: q ∈ maximal_set := by
              simp only [maximal_set]
              rw [Set.mem_sUnion]
              use new_set
              refine ⟨?_, ?_⟩
              simp only [Set.mem_setOf_eq]
              use p
              use (min b_q d)
              refine ⟨rfl, ?_, ?_⟩
              rw [RestrictsToPolyBundleOn] at new_restricts
              rw [RestrictsToPoly]
              use full_poly
              intro y hy
              simp at hy
              have y_cases_a_q: y ≤ a_q ∨ y > a_q := le_or_gt _ _


              cases y_cases_a_q with
              | inl y_le_a_q =>
                have y_in_set: y ∈ Set.Ioo p q := by
                  rw [Set.mem_Ioo]
                  refine ⟨?_, ?_⟩
                  linarith
                  linarith
                specialize h_full_poly y y_in_set
                exact h_full_poly
              | inr y_gt_a_q =>
                have y_in_set: y ∈ Set.Ioo a_q b_q := by
                  rw [Set.mem_Ioo]
                  refine ⟨?_, ?_⟩
                  linarith
                  linarith
                specialize hq_poly y y_in_set
                rw [polys_eq] at hq_poly
                exact hq_poly

              refine ⟨x_in_new, ?_⟩
              simp only [new_set]
              rw [Set.Ioo_subset_Ioo_iff]
              refine ⟨?_, ?_⟩
              rw [Set.Ioo_subset_Ioo_iff] at pq_subset_cd
              linarith
              linarith
              simp
              simp
              refine ⟨?_, ?_⟩
              linarith
              linarith
              simp [new_set]
              refine ⟨?_, ?_, ?_⟩
              linarith
              linarith
              linarith







            rw [maximal_set_eq] at q_in_maximal
            simp at q_in_maximal
            -- END HORRIBLE COPY-PASTE --


        cases p_or_q_in with
        | inl p_in_inter =>
          have pq_poly_on_dup := pq_poly_on
          obtain ⟨pq_poly, h_pq_poly⟩ := pq_poly_on
          let k := pq_poly.natDegree
          let pq_deriv := (⇑Polynomial.derivative)^[k] pq_poly

          have degree_bot_or_other: pq_poly.degree = ⊥ ∨ pq_poly.degree ≠ ⊥ := by
            exact Classical.em (pq_poly.degree = ⊥)


          -- "If f is a polynomial of degree k on (ai,bi), then f(k) is a nonzero constant on (ai,bi)"
          -- but this requires that f not be the zero polynomial.
          -- However, we're trying to show that f^(n) = 0 on (a_i, b_i) = (p, q), which is still true
          -- in the case where f is the zero polynomial
          have poly_deriv_n_zero: (⇑Polynomial.derivative)^[n_x_int] pq_poly = 0 := by
            cases degree_bot_or_other with
            | inl degree_bot =>
              have pq_poly_eq_zero: pq_poly = 0 := Polynomial.degree_eq_bot.mp degree_bot
              rw [pq_poly_eq_zero]
              rw [Polynomial.iterate_derivative_zero]
            | inr degree_not_bot =>
              have pq_deriv_degree_zero: ((⇑Polynomial.derivative)^[k] pq_poly).degree = 0 := by
                apply iter_deriv_degree_zero
                simp only [k]
                apply Polynomial.degree_eq_natDegree
                apply Polynomial.degree_ne_bot.mp degree_not_bot

              have pq_deriv_const: pq_deriv = Polynomial.C (pq_deriv.coeff 0) := by
                apply Polynomial.eq_C_of_degree_eq_zero pq_deriv_degree_zero
              have coeff_nonzero: pq_deriv.coeff 0 ≠ 0 := by
                apply Polynomial.coeff_ne_zero_of_eq_degree pq_deriv_degree_zero

              have pq_deriv_const: ∀ y, pq_deriv.eval y = pq_deriv.coeff 0 := by
                rw [pq_deriv_const]
                simp only [Polynomial.eval_C]
                simp
              have pq_deriv_eval_eq_deriv: ∀ y, y ∈ Set.Ioo p q → pq_deriv.eval y = (iteratedDeriv (pq_poly.natDegree) pq_poly.eval) y := by
                rw [poly_iterated_deriv]
                simp only [pq_deriv]
                simp

              have pq_deriv_eq_f_deriv: ∀ y, y ∈ Set.Ioo p q → pq_deriv.eval y = (iteratedDeriv (pq_poly.natDegree) f) y := by
                intro y hy
                specialize pq_deriv_eval_eq_deriv y hy
                rwa [← iterated_deriv_eq_f_poly (f := f) pq_poly.natDegree pq_poly (Set.Ioo p q) (uniqueDiffOn_Ioo p q) isOpen_Ioo] at pq_deriv_eval_eq_deriv
                rwa [RestrictsToPolyBundleOn]
                exact hy

              have f_deriv_const: ∀ y, y ∈ Set.Ioo p q → (iteratedDeriv pq_poly.natDegree f) y = pq_deriv.coeff 0 := by
                intro y hy
                specialize pq_deriv_eq_f_deriv y hy
                rw [pq_deriv_const] at pq_deriv_eq_f_deriv
                rw [← pq_deriv_eq_f_deriv]

              have f_deriv_eq_at_p: (iteratedDeriv pq_poly.natDegree f) p = pq_deriv.coeff 0 := by
                apply const_ioo_implies_endpoint_left p q (pq_deriv.coeff 0) p_lt_q
                have continuous_deriv := by
                  apply ContDiff.continuous_iteratedDeriv k hCInfinity
                  simp
                apply Continuous.continuousOn continuous_deriv
                apply f_deriv_const



              have deriv_nonzero: ∀ y, y ∈ Set.Ioo p q → iteratedDeriv pq_poly.natDegree f y ≠ 0 := by
                intro y hy
                specialize pq_deriv_eq_f_deriv y hy
                rw [pq_deriv_const] at pq_deriv_eq_f_deriv
                rw [← pq_deriv_eq_f_deriv]
                exact coeff_nonzero

              have poly_degree_lt: pq_poly.natDegree < n_x_int := by
                by_contra!
                have zero_forall_gt := zero_forall_m pq_poly.natDegree p this p_in_inter
                specialize pq_deriv_const p
                have eval_nonzero: Polynomial.eval p pq_deriv  ≠ 0 := by
                  rw [pq_deriv_const]
                  exact coeff_nonzero

                have coeff_eq_zero: pq_deriv.coeff 0 = 0 := by
                  rw [zero_forall_gt] at f_deriv_eq_at_p
                  exact f_deriv_eq_at_p.symm

                contradiction
              apply Polynomial.iterate_derivative_eq_zero poly_degree_lt


          have deriv_eval_eq_zero: ((⇑Polynomial.derivative)^[n_x_int] pq_poly).eval x = 0 := by
            rw [poly_deriv_n_zero]
            simp

          have iterated_poly_zeriv_zero: (iteratedDeriv n_x_int pq_poly.eval) x = 0 := by
            rw [poly_iterated_deriv]
            simp
            exact deriv_eval_eq_zero


          rwa [← iterated_deriv_eq_f_poly (f := f) _ pq_poly (Set.Ioo p q) (uniqueDiffOn_Ioo p q) isOpen_Ioo] at iterated_poly_zeriv_zero
          rw [RestrictsToPolyOn] at pq_poly_on_dup
          rwa [RestrictsToPolyBundleOn]
          exact x_in_pq
        | inr q_in_inter =>
          -- BEGIN HORRIBLE COPY-PASTE --

          have pq_poly_on_dup := pq_poly_on
          obtain ⟨pq_poly, h_pq_poly⟩ := pq_poly_on
          let k := pq_poly.natDegree
          let pq_deriv := (⇑Polynomial.derivative)^[k] pq_poly

          have degree_bot_or_other: pq_poly.degree = ⊥ ∨ pq_poly.degree ≠ ⊥ := by
            exact Classical.em (pq_poly.degree = ⊥)


          -- "If f is a polynomial of degree k on (ai,bi), then f(k) is a nonzero constant on (ai,bi)"
          -- but this requires that f not be the zero polynomial.
          -- However, we're trying to show that f^(n) = 0 on (a_i, b_i) = (p, q), which is still true
          -- in the case where f is the zero polynomial
          have poly_deriv_n_zero: (⇑Polynomial.derivative)^[n_x_int] pq_poly = 0 := by
            cases degree_bot_or_other with
            | inl degree_bot =>
              have pq_poly_eq_zero: pq_poly = 0 := Polynomial.degree_eq_bot.mp degree_bot
              rw [pq_poly_eq_zero]
              rw [Polynomial.iterate_derivative_zero]
            | inr degree_not_bot =>
              have pq_deriv_degree_zero: ((⇑Polynomial.derivative)^[k] pq_poly).degree = 0 := by
                apply iter_deriv_degree_zero
                simp only [k]
                apply Polynomial.degree_eq_natDegree
                apply Polynomial.degree_ne_bot.mp degree_not_bot

              have pq_deriv_const: pq_deriv = Polynomial.C (pq_deriv.coeff 0) := by
                apply Polynomial.eq_C_of_degree_eq_zero pq_deriv_degree_zero
              have coeff_nonzero: pq_deriv.coeff 0 ≠ 0 := by
                apply Polynomial.coeff_ne_zero_of_eq_degree pq_deriv_degree_zero

              have pq_deriv_const: ∀ y, pq_deriv.eval y = pq_deriv.coeff 0 := by
                rw [pq_deriv_const]
                simp only [Polynomial.eval_C]
                simp
              have pq_deriv_eval_eq_deriv: ∀ y, y ∈ Set.Ioo p q → pq_deriv.eval y = (iteratedDeriv (pq_poly.natDegree) pq_poly.eval) y := by
                rw [poly_iterated_deriv]
                simp only [pq_deriv]
                simp

              have pq_deriv_eq_f_deriv: ∀ y, y ∈ Set.Ioo p q → pq_deriv.eval y = (iteratedDeriv (pq_poly.natDegree) f) y := by
                intro y hy
                specialize pq_deriv_eval_eq_deriv y hy
                rwa [← iterated_deriv_eq_f_poly (f := f) pq_poly.natDegree pq_poly (Set.Ioo p q) (uniqueDiffOn_Ioo p q) isOpen_Ioo] at pq_deriv_eval_eq_deriv
                rwa [RestrictsToPolyBundleOn]
                exact hy

              have f_deriv_const: ∀ y, y ∈ Set.Ioo p q → (iteratedDeriv pq_poly.natDegree f) y = pq_deriv.coeff 0 := by
                intro y hy
                specialize pq_deriv_eq_f_deriv y hy
                rw [pq_deriv_const] at pq_deriv_eq_f_deriv
                rw [← pq_deriv_eq_f_deriv]

              have f_deriv_eq_at_q: (iteratedDeriv pq_poly.natDegree f) q = pq_deriv.coeff 0 := by
                apply const_ioo_implies_endpoint_right p q (pq_deriv.coeff 0) p_lt_q
                have continuous_deriv := by
                  apply ContDiff.continuous_iteratedDeriv k hCInfinity
                  simp
                apply Continuous.continuousOn continuous_deriv
                apply f_deriv_const



              have deriv_nonzero: ∀ y, y ∈ Set.Ioo p q → iteratedDeriv pq_poly.natDegree f y ≠ 0 := by
                intro y hy
                specialize pq_deriv_eq_f_deriv y hy
                rw [pq_deriv_const] at pq_deriv_eq_f_deriv
                rw [← pq_deriv_eq_f_deriv]
                exact coeff_nonzero

              have poly_degree_lt: pq_poly.natDegree < n_x_int := by
                by_contra!
                have zero_forall_gt := zero_forall_m pq_poly.natDegree q this q_in_inter
                specialize pq_deriv_const q
                have eval_nonzero: Polynomial.eval q pq_deriv  ≠ 0 := by
                  rw [pq_deriv_const]
                  exact coeff_nonzero

                have coeff_eq_zero: pq_deriv.coeff 0 = 0 := by
                  rw [zero_forall_gt] at f_deriv_eq_at_q
                  exact f_deriv_eq_at_q.symm

                contradiction
              apply Polynomial.iterate_derivative_eq_zero poly_degree_lt


          have deriv_eval_eq_zero: ((⇑Polynomial.derivative)^[n_x_int] pq_poly).eval x = 0 := by
            rw [poly_deriv_n_zero]
            simp

          have iterated_poly_zeriv_zero: (iteratedDeriv n_x_int pq_poly.eval) x = 0 := by
            rw [poly_iterated_deriv]
            simp
            exact deriv_eval_eq_zero


          rwa [← iterated_deriv_eq_f_poly (f := f) _ pq_poly (Set.Ioo p q) (uniqueDiffOn_Ioo p q) isOpen_Ioo] at iterated_poly_zeriv_zero
          rw [RestrictsToPolyOn] at pq_poly_on_dup
          rwa [RestrictsToPolyBundleOn]
          exact x_in_pq
          -- END HORRIBLE COPY-PASTE--
      | inr empty =>
        rw [empty] at hx
        simp at hx


    have deriv_zero_on_cd_omega: ∀ (x : ℝ), x ∈ Set.Ioo c d → (iteratedDeriv n_x_int f) x = 0 := by
      intro x hx
      have x_in_omega_or_x: x ∈ poly_omega ∨ x ∈ X := by
        simp [X]
        exact Classical.em (x ∈ poly_omega)
      cases x_in_omega_or_x with
      | inl x_in_omega =>
        apply deriv_zero_on_cd_int_omega x
        simp
        exact ⟨hx, x_in_omega⟩
      | inr x_in_X =>
        apply x_zero_on_cd_intersect x
        exact ⟨hx, x_in_X⟩


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



    obtain ⟨q, hq⟩ := Set.nonempty_def.mp cd_intersect_x_nonempty
    have _: q ∈ X := by
      apply hq.2
    have _: q ∈ poly_omega := by
      apply cd_subset_omega
      exact hq.1

    contradiction


  have poly_full: poly_omega = (Set.univ) := by
    exact Set.compl_empty_iff.mp X_empty

  have zero_one_subset_poly: Set.Ioo 0 1 ⊆ poly_omega := by
    simp [poly_full]
  simp only [poly_omega] at zero_one_subset_poly

  have zero_one_nonemoty: (Set.Ioo (0: ℝ) 1).Nonempty := by
    exact Set.nonempty_Ioo.mpr zero_lt_one

  obtain ⟨the_final_poly, h_the_final_poly⟩ := omega_r_imp_poly (f := f) 0 1 zero_one_nonemoty hCInfinity zero_one_subset_poly
  simp only [RestrictsToPoly]
  use the_final_poly


#print axioms infinite_zero_is_poly
