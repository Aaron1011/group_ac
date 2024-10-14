import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.DenselyOrdered

open Topology
open Filter

variable {α : Type u} {a b: α} [LinearOrder α] [TopologicalSpace α]

lemma Iic_not_open [OrderTopology α] [DenselyOrdered α] [NoMaxOrder α]: ¬ IsOpen (Set.Iic a) := by
  apply not_imp_not.mpr IsOpen.inter_frontier_eq
  rw [frontier_Iic, Set.inter_singleton_eq_empty, Set.mem_Iic, Classical.not_not]

lemma Ici_not_open [OrderTopology α] [DenselyOrdered α] [NoMinOrder α] : ¬ IsOpen (Set.Ici a) := Iic_not_open (α := αᵒᵈ)

lemma Ioc_not_open [OrderTopology α] [DenselyOrdered α] [NoMaxOrder α] (hab: a < b): ¬ IsOpen (Set.Ioc a b) := by
  apply not_imp_not.mpr IsOpen.inter_frontier_eq
  simp_rw [frontier_Ioc hab, Set.eq_empty_iff_forall_not_mem, Set.mem_inter_iff, Set.mem_Ioc, not_forall, Classical.not_not]
  refine ⟨b, ⟨hab, le_refl _⟩, by simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]⟩

lemma Ico_not_open [DenselyOrdered α] [NoMinOrder α] [OrderTopology α] (hab: a < b): ¬ IsOpen (Set.Ico a b) := by
  simpa only [Set.Ioc, and_comm] using (Ioc_not_open (α := αᵒᵈ) (LT.lt.dual hab))

lemma Icc_not_open [OrderTopology α] [DenselyOrdered α] [OrderClosedTopology α] [NoMinOrder α] [NoMaxOrder α] (hab: a ≤ b): ¬ IsOpen (Set.Icc a b) := by
  have hb: b ∈ (Set.Icc a b) ∩ frontier (Set.Icc a b) := by
    rw [frontier_Icc hab, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_Icc]
    simpa only [le_refl, and_true, or_true]

  exact not_imp_not.mpr IsOpen.inter_frontier_eq (Set.nonempty_iff_ne_empty.mp ⟨b, hb⟩)
