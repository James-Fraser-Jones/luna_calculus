import tactic

namespace named

  --variables come from any type with decidable equality
  --free variables are defined by a finite set of elements of this type
  variables {vs : Type} [decidable_eq vs] {fvs : finset vs}

  inductive expr : finset vs → Type
  | var (v : vs) (v ∈ fvs) : expr fvs
  | app (t : expr fvs) (u : expr fvs) : expr fvs
  | lam (v : vs) (b : expr fvs) : expr ({v} ∪ fvs)
  open expr

  inductive is_abs {v} : expr ({v} ∪ fvs) → Prop
  | abs (b : expr fvs) : is_abs (lam v b)

  def abs := {e : expr fvs // is_abs e}
end named