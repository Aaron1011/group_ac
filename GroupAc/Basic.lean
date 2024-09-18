import Mathlib.Data.Set.Defs
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Logic.Embedding.Basic


universe u
variable {α : Type u}
variable {d : α -> α -> Prop}

variable [Group G]

#check α → Prop
#check Set α
#check Set (Set α)

theorem group_implies_ac (h: ∀ s: Set α, (∃ G, ∃ f: (s -> Group G), Function.Bijective f)): True := by
  G.mul 0 1
  sorry


def Set.image' {α : Type _} {β : Type _} (s : Set α) (f : (a : α) → a ∈ s → β) : Set β :=
  {b | ∃ a ha, f a ha = b}

def hartog_number (s: Set α) : Set Ordinal.{u} :=
  let prod := Set.prod s s
  let pow_prod := Set.powerset prod
  let related_fun := Set.image (fun c => (fun x y => (x, y) ∈ c)) pow_prod
  let well_ords := {β ∈ related_fun | IsWellOrder α β}
  Set.image' well_ords (fun c hc => by
      rw [Set.mem_setOf_eq] at hc
      apply And.right at hc
      apply Ordinal.type c
  )
  --{Ordinal.type c | (c: α -> α -> Prop)}
  --have hd: d ∈ well_ords → IsWellOrder α d := by
  --  intro h
  --  rw [Set.mem_setOf_eq] at h
  --  exact h.2
  --let my_ords := (fun c => Ordinal.type c) '' well_ords
  --my_ords


  --let my_ords := (fun c => Ordinal.type c) '' {β ∈ related_fun | IsWellOrder α β}
  --by
  --  intro x
  --  have xs: x ∈ well_ords := by refl
  --  rw [Set.mem_setOf_eq] at well_ords


  --have new_well_ord: Ordinal.type '' well_ord := by
  --  sorry
  --well_ord
  --by apply Set.mem_image_of_mem (fun c => Ordinal.type c) {β ∈ related_fun | IsWellOrder α β}
  --as_ord
  --as_ord
  -- (fun c => Ordinal.type c) '' as_ord by
  --  sorry

theorem le_hartog (s: Set α) : Cardinal.lift.{u + 1} (Cardinal.mk s) < Cardinal.mk (hartog_number s) :=
  --simp only [(· ≤ ·)]
  rw [← not_le]
  intro h
  rw [Cardinal.out_embedding] at h
  let f: _ := Classical.choice h



  --simp only [(· ≤ ·)] at h
  --rw [← Cardinal.lift_lt] at h




-- def hartog_cardinality (s: Set α) : ¬(hartog_number s < Cardinal.mk s) := by
--   rw [hartog_number]
--   simp only [(· < ·)]
--   contrapose!
--   simp
--   intro ⟨α⟩



  -- suffices (fun α β ↦ Nonempty (α ↪ β)) from simp

  --simp
  --apply Set.isEmpty_coe_sort
  --rw [Set.empty_def]
