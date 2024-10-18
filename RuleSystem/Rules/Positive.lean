import RuleSystem.Rules.Basic

namespace Rule

def IsPositive {n : ℕ} (rule : Rule n) : Prop :=
  match rule with
  | .positive _ => True
  | .negative _ => False

theorem isPositive_of_positive {n : ℕ} (tags : Tags n) : IsPositive (positive tags) := by simp [IsPositive]
theorem isPositive_of_eq_positive {n : ℕ} {tags : Tags n} {rule : Rule n} (h : rule = positive tags)
  : IsPositive rule := h ▸ isPositive_of_positive _

def Positive (n : ℕ) := Subtype (@IsPositive n)

namespace Positive

def fromTags {n : ℕ} (tags : Tags n) : Positive n := ⟨Rule.positive tags, by simp only [Rule.IsPositive]⟩

def fromTagsEmbedding {n : ℕ} : Tags n ↪ Positive n :=
  let fromTags_inj : fromTags.Injective := by
    intro t t' subtype_eq
    have := Subtype.eq_iff.mp subtype_eq
    simp only [fromTags, positive.injEq] at this
    assumption
  ⟨fromTags, fromTags_inj⟩

end Positive

-- TODO: Why is this not found if we don't explicitly define it here? E.g. `captureOnTagged (toPositive rule)` does not
--       type check without this
instance instCoeOutPositiveRules {n : ℕ} : CoeOut (Finset (Positive n)) (Rules n) := Finset.instCoeOutSubtype

end Rule
