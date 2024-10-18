import RuleSystem.Rules.Negative
import RuleSystem.Rules.Positive

namespace Rule

-- def split {n : ℕ} (rule : Rule n) : Finset (Rule n) :=
--   match rule with
--   | .positive tags => tags.map positive
--   | .negative tags => tags.map negative

namespace Negative

def toPositives {n : ℕ} (rule : Negative n) : Finset (Positive n) :=
  let tags' := (tags rule.val)ᶜ
  -- -- TODO: Use `Positive.fromTagsEmbedding` here
  -- let ctor := λ (tag : Tag n) ↦ Positive.fromTags {tag}
  -- let ctor_inj : ctor.Injective := by
  --   intro t t' subtype_eq
  --   have := Subtype.eq_iff.mp subtype_eq
  --   simp only [Positive.fromTags, positive.injEq, Finset.singleton_inj, ctor] at this
  --   assumption
  Finset.map Positive.fromTagEmbedding tags'

end Negative

end Rule
