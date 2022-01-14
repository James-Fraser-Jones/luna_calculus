import tactic
import data.buffer.parser

namespace varonly

  inductive term : Type
  | Z : term
  | S : term → term
  | R : term → term
  | var : term → term
  | bin : term → term
  | app : term → term → term
  | abs : term → term → term
  open term

  inductive is_numeral : term → Prop
  | z : is_numeral Z
  | s {t} (h : is_numeral t) : is_numeral (S t)
  open is_numeral

  instance {t} : decidable (is_numeral t) := begin
    induction t,

    right,
    exact is_numeral.z,

    case S : t h {
      cases h,
      left,
      intro p,
      apply h,
      cases p,
      assumption,
      right,
      apply is_numeral.s,
      assumption,
    },

    repeat {
      left,
      intro p,
      cases p,
    },
  end

  def numeral := {n : term // is_numeral n}

  inductive is_identifier : term → Prop
  | n {t} (h : is_numeral t) : is_identifier t
  | r {t} (h : is_identifier t) : is_identifier (R t)
  open is_identifier

  instance {t} : decidable (is_identifier t) := begin
    induction t,

    right,
    apply n,
    apply z,

    case S : t h {
      left,
      intro p,
      cases h,

      apply h,
      cases p,
      cases p_h,
      apply n,
      assumption,

      cases p,
    }
  end

  def identifier := {i : term // is_identifier i}

  def show_term : term → string
  | Z := "a"
  | (S t) := "S " ++ show_term t
  | (R t) := show_term t ++ "'"
  | (var t) := "# " ++ show_term t
  | (bin t) := "λ " ++ show_term t
  | (app t u) := show_term t ++ " " ++ show_term u
  | (abs t u) := show_term t ++ " → " ++ show_term u

  instance : has_repr term := ⟨show_term⟩

  def example1 : term := R $ R Z
  #eval example1

  #check @parser.run

end varonly