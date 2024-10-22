import RuleSystem.Rules.Negative
import RuleSystem.Rules.Theorems.Basic

namespace Rule.Negative

def castSucc {n : ℕ} (rule : Negative n) : Negative (n + 1) := fromTags (rule.val.tags.map Fin.castSuccEmb)

def castSuccEmbedding {n : ℕ} : Negative n ↪ Negative (n + 1) :=
  let castSucc_inj : castSucc.Injective := by
    intro t t' subtype_eq
    obtain ⟨tags, t_val_eq⟩ := exists_val_eq_negative t
    obtain ⟨tags', t'_val_eq⟩ := exists_val_eq_negative t'
    simp [castSucc, fromTags, Rule.tags, t_val_eq, t'_val_eq] at subtype_eq
    apply Subtype.eq_iff.mpr
    rw [t_val_eq, t'_val_eq]
    simpa [negative]
  ⟨castSucc, castSucc_inj⟩

end Rule.Negative
