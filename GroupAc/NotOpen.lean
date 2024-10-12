
import Mathlib
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.Basic

open Topology
open Filter

lemma general_iic_not_open  {α : Type u} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α] [PreconnectedSpace α]  (a: α) (ha: ¬ IsMax a) : ¬ IsOpen (Set.Iic a) := by
  have is_closed: IsClosed (Set.Iic a) := isClosed_Iic
  have nonempty: (Set.Iic a).Nonempty := by simp only [Set.nonempty_Iic]

  have ici_not_univ: Set.Iic a ≠ Set.univ := by
    simp only [Set.ne_univ_iff_exists_not_mem, Set.mem_Iic, not_le]
    apply not_isMax_iff.mp ha

  have not_clopen: ¬IsClopen (Set.Iic a) := by
    apply (not_imp_not.mpr isClopen_iff.mp)
    rw [not_or]
    exact ⟨Set.Nonempty.ne_empty nonempty, ici_not_univ⟩

  rw [IsClopen, not_and] at not_clopen
  exact not_clopen is_closed


-- (-↔, a]
-- [a, +↔)

--lemma new_general_ici_not_open  {α : Type u} (a: ℝ) (ha: ¬ IsMin a) : ¬ IsOpen (Set.Ici a) := by

-- Bug - when duplicate 'ha' hypothsis names, 'exact' doesn't work
-- lemma exact_question_bug_general_ici_not_open  {α : Type u} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α] (ha: PreconnectedSpace α) (a: α) (ha: ¬ IsMin a) : ¬ IsOpen (Set.Ici a) := by
--   have is_dual: PreconnectedSpace αᵒᵈ := by exact? -- Suggests 'exact ha', doesn't work
--   apply general_iic_not_open (α := αᵒᵈ) a ha

--variable {β} [TopologicalSpace β] [LinearOrder β] [OrderClosedTopology β] [hq: PreconnectedSpace β]
--#synth PreconnectedSpace βᵒᵈ

--set_option trace.Meta.synthInstance true

instance instPreconnected (α : Type*) [TopologicalSpace α] [hq: PreconnectedSpace α] : PreconnectedSpace αᵒᵈ := ‹_›


lemma general_ici_not_open  {α : Type u} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α] [PreconnectedSpace α] (a: α) (ha: ¬ IsMin a) : ¬ IsOpen (Set.Ici a) := by
  -- have is_dual: PreconnectedSpace αᵒᵈ := by assumption
  have some_result := general_iic_not_open (α := αᵒᵈ) a ha
  -- TODO: Figure out how this works
  have in_regular: ¬ IsOpen (Set.Ici a) := some_result
  apply in_regular


-- Missing 'open Set' implies undefined univ, weird error here
lemma not_preconnected {α: Type u} [TopologicalSpace α] (ha: ¬(PreconnectedSpace α)) : (¬ IsPreconnected (Set.univ : Set α)) := by
  intro hz
  have is_preconnected: PreconnectedSpace α := ⟨hz⟩
  contradiction


-- (a, b] [a, b)

lemma general_ioc_not_open {α: Type*} [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α] [NoMaxOrder α] [OrderTopology α] [PreconnectedSpace α] (a b: α) (hab: a < b): ¬ IsOpen (Set.Ioc a b) := by
  have frontier_eq: frontier (Set.Ioc a b) = {a, b} := by apply frontier_Ioc hab
  have frontier_imp_not_open: ¬((Set.Ioc a b) ∩ frontier (Set.Ioc a b) = ∅) → ¬ IsOpen (Set.Ioc a b) := not_imp_not.mpr IsOpen.inter_frontier_eq
  have b_in_ioc: b ∈ Set.Ioc a b := by
    rw [Set.mem_Ioc]
    refine ⟨hab, ?_⟩
    simp
  have intersect_frontier: b ∈ (Set.Ioc a b) ∩ frontier (Set.Ioc a b) := by
    rw [frontier_eq]
    simp [b_in_ioc]

  have frontier_intersect_nonempty: Set.Nonempty ((Set.Ioc a b) ∩ frontier (Set.Ioc a b)):= by
    refine ⟨b, intersect_frontier⟩

  have not_eq_empty: ¬((Set.Ioc a b) ∩ frontier (Set.Ioc a b) = ∅) := by
    exact Set.nonempty_iff_ne_empty.mp frontier_intersect_nonempty

  apply frontier_imp_not_open not_eq_empty

lemma general_ico_not_open {α: Type*} [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α] [NoMinOrder α] [OrderTopology α] [PreconnectedSpace α] (a b: α) (hab: a < b): ¬ IsOpen (Set.Ico a b) := by
  have frontier_eq: frontier (Set.Ico a b) = {a, b} := by apply frontier_Ico hab
  have frontier_imp_not_open: ¬((Set.Ico a b) ∩ frontier (Set.Ico a b) = ∅) → ¬ IsOpen (Set.Ico a b) := not_imp_not.mpr IsOpen.inter_frontier_eq
  have a_in_ico: a ∈ Set.Ico a b := by
    rw [Set.mem_Ico]
    refine ⟨?_, hab⟩
    simp
  have intersect_frontier: a ∈ (Set.Ico a b) ∩ frontier (Set.Ico a b) := by
    rw [frontier_eq]
    simp [a_in_ico]

  have frontier_intersect_nonempty: Set.Nonempty ((Set.Ico a b) ∩ frontier (Set.Ico a b)):= by
    refine ⟨a, intersect_frontier⟩

  have not_eq_empty: ¬((Set.Ico a b) ∩ frontier (Set.Ico a b) = ∅) := by
    exact Set.nonempty_iff_ne_empty.mp frontier_intersect_nonempty

  apply frontier_imp_not_open not_eq_empty

lemma lt_iff_neg (a b: ℝ): a < b ↔ -b < -a := by
  simp only [neg_lt_neg_iff]

lemma dual_general_ico_not_open {α: Type*}
  [AddGroup α]
  [ht: TopologicalSpace α]
  [h_linear: LinearOrder α] [hd: DenselyOrdered α] [h_mo_min: NoMinOrder α] [NoMaxOrder α] [OrderTopology α] [PreconnectedSpace α]
  [CovariantClass α α (fun x1 x2 ↦ x1 + x2) fun x1 x2 ↦ x1 < x2]
  [CovariantClass α α (Function.swap fun x1 x2 ↦ x1 + x2) fun x1 x2 ↦ x1 < x2]
  (a b: α) (hab: a < b): ¬ IsOpen (Set.Ico a b) := by

    have dual_a_lt_b: (OrderDual.toDual b) < (OrderDual.toDual a) := by
      simp only [OrderDual.toDual_lt_toDual]
      apply neg_lt_neg_iff.mp
      simp
      assumption

    have something := general_ioc_not_open (α := αᵒᵈ) b a dual_a_lt_b
    rw [Set.Ioc] at something
    rw [Set.Ico]
    simp only [and_comm] at something
    apply something
