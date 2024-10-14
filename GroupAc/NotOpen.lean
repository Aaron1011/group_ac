import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.DenselyOrdered

open Topology
open Filter

/-- A set with a point in both the frontier and the set is not open -/
private lemma frontier_to_not_IsOpen {β: Type u} [TopologicalSpace β] {s: Set β} {a: β} (hb: a ∈ s) (hf: a ∈ frontier s): ¬ IsOpen s := by
  apply not_imp_not.mpr IsOpen.inter_frontier_eq
  simp_rw [Set.eq_empty_iff_forall_not_mem, Set.mem_inter_iff, not_forall, Classical.not_not]
  refine ⟨a, ⟨hb, hf⟩⟩


variable {α : Type u} {a b: α} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]  [DenselyOrdered α]

theorem not_IsOpen_Iic [NoMaxOrder α]: ¬ IsOpen (Set.Iic a) := by
  apply not_imp_not.mpr IsOpen.inter_frontier_eq
  rw [frontier_Iic, Set.inter_singleton_eq_empty, Set.mem_Iic, Classical.not_not]

theorem not_IsOpen_Ici [NoMinOrder α] : ¬ IsOpen (Set.Ici a) := not_IsOpen_Iic (α := αᵒᵈ)

theorem not_IsOpen_Ioc [NoMaxOrder α] (h: a < b): ¬ IsOpen (Set.Ioc a b) :=
  frontier_to_not_IsOpen (Set.mem_Ioc.mpr ⟨h, le_refl _⟩) (by simp [frontier_Ioc h])

theorem not_IsOpen_Ico [NoMinOrder α] (h: a < b): ¬ IsOpen (Set.Ico a b) := by
  simpa only [Set.Ioc, and_comm] using (not_IsOpen_Ioc (α := αᵒᵈ) (LT.lt.dual h))

theorem not_IsOpen_Icc [NoMinOrder α] [NoMaxOrder α] (h: a ≤ b): ¬ IsOpen (Set.Icc a b) :=
  frontier_to_not_IsOpen (Set.mem_Icc.mpr ⟨h, le_refl _⟩) (by simp [frontier_Icc h])
