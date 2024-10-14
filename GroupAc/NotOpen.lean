import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.DenselyOrdered

open Topology
open Filter

variable {α : Type u} {a: α} [LinearOrder α]

lemma Set.Iic.ne_univ_of_not_isMax (ha: ¬ IsMax a) : Set.Iic a ≠ Set.univ :=
  (Set.ne_univ_iff_exists_not_mem _).mpr <| by simpa using not_isMax_iff.mp ha

variable [TopologicalSpace α] [OrderTopology α]

lemma Iic_not_open [DenselyOrdered α] [NoMaxOrder α]: ¬ IsOpen (Set.Iic a) := by
  simp? [not_imp_not.mpr IsOpen.inter_frontier_eq, frontier_Iic]


   --simp [not_imp_not.mpr IsOpen.inter_frontier_eq, frontier_Iic]


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

lemma Ici_not_open [DenselyOrdered α] [NoMinOrder α] : ¬ IsOpen (Set.Ici a) := Iic_not_open (α := αᵒᵈ)

-- Missing 'open Set' implies undefined univ, weird error here
lemma not_preconnected {α: Type u} [TopologicalSpace α] (ha: ¬(PreconnectedSpace α)) : (¬ IsPreconnected (Set.univ : Set α)) := by
  intro hz
  have is_preconnected: PreconnectedSpace α := ⟨hz⟩
  contradiction


-- (a, b] [a, b)

lemma general_ioc_not_open {α: Type*} [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α] [NoMaxOrder α] [OrderTopology α] (a b: α) (hab: a < b): ¬ IsOpen (Set.Ioc a b) := by
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

lemma general_ico_not_open {α: Type*} [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α] [NoMinOrder α] [OrderTopology α] (a b: α) (hab: a < b): ¬ IsOpen (Set.Ico a b) := by
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

lemma dual_general_ico_not_open {α: Type*}
  [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α] [NoMinOrder α] [OrderTopology α]
  (a b: α) (hab: a < b): ¬ IsOpen (Set.Ico a b) := by
    have something := general_ioc_not_open (α := αᵒᵈ) b a hab
    simp only [Set.Ico, and_comm]
    simp only [Set.Ioc, and_comm] at something
    apply something
