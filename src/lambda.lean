import tactic

--lambda expressions that track max number of distinct free variables
inductive lambda : ℕ → Type
| var {n : ℕ} (n' : ℕ) (h : n' < n) : lambda n
| app {n : ℕ} (t : lambda n) (u : lambda n) : lambda n
| lam {n : ℕ} (t : lambda (n+1)) : lambda n

namespace lambda

  def min_var (n : ℕ) : lambda (n+1) := var n (lt_add_one n)

  def combinator := lambda 0

  def id : combinator := lam (min_var 0)

  def lift : ∀ {n : ℕ} (k : ℕ), lambda n → lambda (n+k)
  | _ 0 t := t
  | _ (k+1) (var n h) := var n (by {transitivity, assumption, refine lt_of_le_of_lt (nat.le.intro rfl) _, exact k, apply lt_add_one})
  | _ (k+1) (app t u) := app (lift (k+1) t) (lift (k+1) u)
  | _ (k+1) (lam t) := cast (congr_arg lambda (add_right_comm _x 1 k)) (lam (lift (k+1) t))

  def default {n : ℕ} : lambda n := cast (congr_arg lambda (zero_add n)) (lift n id)

  def mk_var {n : ℕ} (n' : ℕ) : lambda n := begin
    by_cases n' + 1 ≤ n,
    exact (cast (begin
      apply congr_arg,
      transitivity,
      symmetry,
      apply nat.add_sub_assoc,
      assumption,
      apply nat.add_sub_cancel_left,
    end) (lift (n - (n'+1)) (min_var n'))),
    exact default, --fail silently by creating lifted identity function instead
  end

  notation # := mk_var

  def sub : ∀ {n : ℕ}, lambda n → lambda n → lambda n
  | n (var n' h) t := if n' + 1 = n then t else var n' h
  | _ (app u v) t := app (sub u t) (sub v t)
  | _ (lam u) t := lam (sub u (lift 1 t))

  def const : combinator := lam (lam (#0))
  def flip : combinator := lam (lam (lam (app (app (#0) (#2)) (#1))))

  #check @monad

end lambda