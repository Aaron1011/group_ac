import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic

open Topology
open Filter

variable {α : Type u} {a: α} [LinearOrder α]

lemma Set.Iic.ne_univ_of_not_isMax (ha: ¬ IsMax a) : Set.Iic a ≠ Set.univ :=
  (Set.ne_univ_iff_exists_not_mem _).mpr <| by simpa using not_isMax_iff.mp ha

variable [TopologicalSpace α] [OrderClosedTopology α] [PreconnectedSpace α]

lemma Iic_not_open (ha: ¬ IsMax a) : ¬ IsOpen (Set.Iic a) :=
  (not_and.mp <| not_imp_not.mpr isClopen_iff.mp <| not_or.mpr <|
    ⟨Set.Nonempty.ne_empty (by simp), Set.Iic.ne_univ_of_not_isMax ha⟩) isClosed_Iic
