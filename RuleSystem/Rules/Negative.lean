import RuleSystem.Rules.Basic

namespace Rule

def IsNegative {n : ℕ} (rule : Rule n) : Prop :=
  match rule with
  | .positive _ => False
  | .negative _ => True

theorem isNegative_of_negative {n : ℕ} (tags : Tags n) : IsNegative (negative tags) := by simp [IsNegative]
theorem isNegative_of_eq_negative {n : ℕ} {tags : Tags n} {rule : Rule n} (h : rule = negative tags)
  : IsNegative rule := h ▸ isNegative_of_negative _

def Negative (n : ℕ) := Subtype (@IsNegative n)

namespace Negative

def fromTags {n : ℕ} (tags : Tags n) : Negative n := ⟨Rule.negative tags, by simp only [Rule.IsNegative]⟩

def fromTagsEmbedding {n : ℕ} : Tags n ↪ Negative n :=
  let fromTags_inj : fromTags.Injective := by
    intro t t' subtype_eq
    have := Subtype.eq_iff.mp subtype_eq
    simp only [fromTags, negative.injEq] at this
    assumption
  ⟨fromTags, fromTags_inj⟩

end Negative

-- TODO: Why is this not found if we don't explicitly define it here?
instance instCoeOutNegativeRules {n : ℕ} : CoeOut (Finset (Negative n)) (Rules n) := Finset.instCoeOutSubtype

end Rule
