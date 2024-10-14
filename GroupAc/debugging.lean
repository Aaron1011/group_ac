import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.DenselyOrdered

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


-- Missing 'open Set' implies undefined univ, weird error here
lemma not_preconnected {α: Type u} [TopologicalSpace α] (ha: ¬(PreconnectedSpace α)) : (¬ IsPreconnected (Set.univ : Set α)) := by
  intro hz
  have is_preconnected: PreconnectedSpace α := ⟨hz⟩
  contradiction


instance instPreconnected (α : Type*) [TopologicalSpace α] [hq: PreconnectedSpace α] : PreconnectedSpace αᵒᵈ := ‹_›
