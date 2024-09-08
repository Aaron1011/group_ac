import Mathlib.Data.Set.Defs
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Ordinal.Basic

universe u
variable {α : Type u}

def hartog_well_orders (s: Set α) : Set (α → α → Prop) :=
  let prod := Set.prod s s
  let pow_prod := Set.powerset prod
  let related_fun := Set.image (fun c => (fun x y => (x, y) ∈ c)) pow_prod
  {β ∈ related_fun | IsWellOrder α β }

def hartog_number (s: Set α): Cardinal :=
  --let ordinals := {Ordinal.type c | c ∈ {β ∈ related_fun | IsWellOrder α β }}
  let ordinals := {c | c ∈ hartog_well_orders s}
  Cardinal.mk ordinals

def hartog_cardinality (s: Set α) : Cardinal.mk s < hartog_number s := by
  rw [← not_le, hartog_number]
  apply Classical.byContradiction
  simp


  --simp
  --apply Set.isEmpty_coe_sort
  --rw [Set.empty_def]
