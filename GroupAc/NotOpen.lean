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
  simp only [Set.nonempty_Ioi, frontier_Iic', Set.inter_singleton_eq_empty, Set.mem_Iic, le_refl,
    not_true_eq_false, not_false_eq_true, not_imp_not.mpr IsOpen.inter_frontier_eq]


lemma Ici_not_open [OrderTopology α] [DenselyOrdered α] [NoMinOrder α] : ¬ IsOpen (Set.Ici a) := Iic_not_open (α := αᵒᵈ)

lemma general_ioc_not_open [OrderTopology α] [DenselyOrdered α] [NoMaxOrder α] (hab: a < b): ¬ IsOpen (Set.Ioc a b) := by
  have intersect_frontier: b ∈ (Set.Ioc a b) ∩ frontier (Set.Ioc a b) := by
    rw [frontier_Ioc hab]
    rw [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_Ioc]
    simp only [le_refl, and_true, or_true]
    exact hab

  exact not_imp_not.mpr IsOpen.inter_frontier_eq (Set.nonempty_iff_ne_empty.mp ⟨b, intersect_frontier⟩)

lemma dual_general_ico_not_open [DenselyOrdered α] [NoMinOrder α] [OrderTopology α] (hab: a < b): ¬ IsOpen (Set.Ico a b) := by
  simpa [Set.Ioc, and_comm] using (general_ioc_not_open (α := αᵒᵈ) (LT.lt.dual hab))
