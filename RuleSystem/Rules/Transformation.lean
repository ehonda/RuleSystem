import RuleSystem.Rules.Negative
import RuleSystem.Rules.Positive

namespace Rule

def split {n : ℕ} (rule : Rule n) : Finset (Rule n) :=
  match rule with
  | .positive tags => tags.map Positive.fromTagEmbedding
  | .negative tags => tags.map Negative.fromTagEmbedding

namespace Negative

-- TODO: Maybe define this in terms of `split`?
def toPositives {n : ℕ} (rule : Negative n) : Finset (Positive n) :=
  (rule.val.tags)ᶜ.map Positive.fromTagEmbedding

end Negative

end Rule
