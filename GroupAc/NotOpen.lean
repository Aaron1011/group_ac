
import Mathlib
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.Basic

open Topology
open Filter

lemma general_iic_not_open  (a: ℝ) (hb: ∃ b, b ∉ (Set.Iic a)) : ¬ IsOpen (Set.Iic a) := by
  have is_closed: IsClosed (Set.Iic a) := isClosed_Iic
  have nonempty: (Set.Iic a).Nonempty := by simp

  have ici_not_univ: Set.Iic a ≠ Set.univ := by
    rw [Set.ne_univ_iff_exists_not_mem]
    exact hb

  have not_clopen: ¬IsClopen (Set.Iic a) := by
    apply (not_imp_not.mpr isClopen_iff.mp)
    simp
    refine ⟨Set.Nonempty.ne_empty nonempty, ici_not_univ⟩

  simp [IsClopen] at not_clopen
  apply not_clopen is_closed
