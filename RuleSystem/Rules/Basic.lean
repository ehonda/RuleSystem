import RuleSystem.Rules.BigOr
import RuleSystem.Rules.Defs
import RuleSystem.Rules.Instance
import Mathlib.Data.Fintype.Basic

namespace Rule

inductive Rule (n : ℕ) where
  | positive (tags : Tags n)
  | negative (tags : Tags n)

abbrev Rules (n : ℕ) := Finset (Rule n)

-- TODO: Is there a better way to extract the tags?
def tags {n : ℕ} (rule : Rule n) : Tags n :=
  match rule with
  | .positive tags => tags
  | .negative tags => tags

def appliesTo {n : ℕ} (rule : Rule n) (inst : Instance n) : Prop :=
  match rule with
  | .positive tags => tags ⊆ inst.tags
  | .negative tags => tags ∩ inst.tags = ∅

-- TODO: Better name
def applyTo {n : ℕ} (rules : Rules n) (inst : Instance n) : Prop :=
  ∃ rule ∈ rules, (appliesTo · inst) rule

def IsPositive {n : ℕ} (rule : Rule n) : Prop :=
  match rule with
  | .positive _ => True
  | .negative _ => False

def Positive (n : ℕ) := {rule : Rule n // IsPositive rule}

def IsNegative {n : ℕ} (rule : Rule n) : Prop :=
  match rule with
  | .positive _ => False
  | .negative _ => True

def Negative (n : ℕ) := {rule : Rule n // IsNegative rule}

def toPositive {n : ℕ} (rule : Negative n) : Finset (Positive n) :=
  let tags' := Finset.univ \ Rule.tags rule.val
  let ctor : Tag n → Positive n := λ (tag : Tag n) ↦ let rule := Rule.positive {tag}
    ⟨rule, by simp only [Rule.IsPositive]⟩
  let ctor_inj : ctor.Injective := by
    -- simp only [Function.Injective, Rule.positive.injEq, Finset.singleton_inj, imp_self, implies_true]
    simp only [Function.Injective]
    intro t t' subtype_eq
    -- TODO: We go `t = t' ↔ {t} = {t'} ↔ Rule.positive {t} = Rule.positive {t'}`. Then we can use `Subtype.mk_eq_mk`
    -- rw [← Rule.positive.injEq]
    -- have := Rule.positive.injEq t.val t'.val subtype_eq
    -- apply (@Subtype.mk_eq_mk _ _ _ True.intro _ True.intro).mp subtype_eq
    sorry
  Finset.map ⟨ctor, ctor_inj⟩ tags'

theorem appliesTo_iff_toPositive_applyTo {n : ℕ} (rule : Negative n) (inst : Instance n) :
  appliesTo rule.val inst ↔ applyTo ((toPositive rule).map (Function.Embedding.subtype _)) inst := by
    sorry

end Rule
