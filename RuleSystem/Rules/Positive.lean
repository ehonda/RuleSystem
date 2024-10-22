import RuleSystem.Rules.Basic
import RuleSystem.Rules.Finset
import RuleSystem.Rules.Function

namespace Rule

def IsPositive {n : ℕ} (rule : Rule n) : Prop :=
  match rule with
  | .positive _ => True
  | .negative _ => False

theorem isPositive_of_positive {n : ℕ} (tags : Tags n) : IsPositive (positive tags) := by simp [IsPositive]
theorem isPositive_of_eq_positive {n : ℕ} {tags : Tags n} {rule : Rule n} (h : rule = positive tags)
  : IsPositive rule := h ▸ isPositive_of_positive _

abbrev Positive (n : ℕ) := Subtype (@IsPositive n)

namespace Positive

def fromTags {n : ℕ} (tags : Tags n) : Positive n := ⟨positive tags, by simp only [IsPositive]⟩

def fromTagsEmbedding {n : ℕ} : Tags n ↪ Positive n :=
  let fromTags_inj : fromTags.Injective := by
    intro t t' subtype_eq
    have := Subtype.eq_iff.mp subtype_eq
    simp only [fromTags, positive.injEq] at this
    assumption
  ⟨fromTags, fromTags_inj⟩

def fromTag {n : ℕ} (tag : Tag n) := fromTags {tag}

def fromTagEmbedding {n : ℕ} : Tag n ↪ Positive n :=
  -- TODO: Find a nicer way to prove this
  let fromTag_inj : fromTag.Injective := by
    intro t t' subtype_eq
    have := Subtype.eq_iff.mp subtype_eq
    simp only [fromTag, positive.injEq] at this
    have := fromTagsEmbedding.inj' (Subtype.eq this)
    exact Finset.singleton_inj.mp this
  ⟨fromTag, fromTag_inj⟩

theorem appliesTo_fromTagEmbedding {n : ℕ} {tag : Tag n} {inst : Instance n}
  : (fromTagEmbedding tag).val.appliesTo inst = ({tag} ⊆ inst.tags) := rfl

end Positive

end Rule
