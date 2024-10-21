import RuleSystem.Rules.Negative
import RuleSystem.Rules.Positive

namespace Rule

def split {n : ℕ} (rule : Rule n) : Finset (Rule n) :=
  match rule with
  | .positive tags => (tags.map Positive.fromTagEmbedding : Finset (Positive n))
  | .negative tags => (tags.map Negative.fromTagEmbedding : Finset (Negative n))

namespace Negative

def toPositives {n : ℕ} (rule : Negative n) : Finset (Positive n) :=
  let tags' := (tags rule.val)ᶜ
  tags'.map Positive.fromTagEmbedding

end Negative

end Rule
