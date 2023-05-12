import GCG.Levels.InfSup.Level_1

Game "GCG"
World "InfSup"
Level 2
Title "Infimums are unique."

variable [PartialOrder X]


Introduction
"
Actually there can be only one inf.
"

LemmaDoc isInf.eq as "isInf.eq" in "InfSup"
"A set has at most one infimum."

Statement isInf.eq "A set has at most one infimum."
 {s : Set X} {x₀ x₁ : X} (hx₀ : isInf s x₀) (hx₁ : isInf s x₁) : x₀ = x₁ := by
  apply le_antisymm
  · exact (hx₁ _).1 ((hx₀ _).2 le_rfl)
  · exact (hx₀ _).1 ((hx₁ _).2 le_rfl)


LemmaTab "InfSup"

Conclusion
"
## Now venture off on your own.

Good luck! Click on \"Next\" to solve some levels on your own.
"
