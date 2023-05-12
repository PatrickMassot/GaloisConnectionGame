import GCG.Metadata
import Mathlib.Data.Set.Lattice

Game "GCG"
World "InfSup"
Level 1
Title "Infimums are lower bounds."

variable [PartialOrder X]

/-- An element `x₀` is an infimum of a set `s` in `X` if every element
of `X` is a lower bound of `s` if and only if it below `x₀`.  -/
def isInf (s : Set X) (x₀ : X) :=
  ∀ x, x ∈ lowerBounds s ↔ x ≤ x₀

DefinitionDoc isInf as "isInf"
"An element `x₀` is an infimum of a set `s` in `X` if every element
of `X` is a lower bound of `s` if and only if it below `x₀`."

LemmaDoc le_rfl as "le_rfl" in "InfSup"
"`le_rfl {a : X} : a ≤ a`"

LemmaDoc le_trans as "le_trans" in "InfSup"
"`le_trans {a b c : X} (h : a ≤ b) (h' : b ≤ c) : a ≤ c`"

LemmaDoc le_antisymm as "le_antisymm" in "InfSup"
"`le_antisymm {a b : X} (h : a ≤ b) (h' : b ≤ a) : a = b`"

Introduction
"
In this world, `X` is a type equiped with a partial order relation. So you have access
to lemmas:
* `le_rfl {a : X} : a ≤ a`
* `le_trans {a b c : X} (h : a ≤ b) (h' : b ≤ c) : a ≤ c`
* `le_antisymm {a b : X} (h : a ≤ b) (h' : b ≤ a) : a = b`
"

Statement isInf.lowerBound "An infimum of a set is a lower bound of that set."
  {s : Set X} {x₀ : X} (h : isInf s x₀) : x₀ ∈ lowerBounds s := by
  rw [h]

LemmaTab "InfSup"

Conclusion
"
## Now venture off on your own.

Good luck! Click on \"Next\" to solve some levels on your own.
"
