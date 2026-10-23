/-
  JSP-000301 — Golomb's question on consecutive powerful numbers.

  Problem: If two consecutive positive integers are powerful, must at least
  one be a square?

  Answer: No. S. W. Golomb ("Powerful numbers", Amer. Math. Monthly 77(8),
  1970) observed that
      12167 = 23^3   and   12168 = 2^3 * 3^2 * 13^2
  are both powerful, and neither is a square, since
      110^2 = 12100 < 12167 < 12168 < 12321 = 111^2.
  (12167 is the smallest such counterexample: verified by exhaustive search
  below 20000, where it is the unique n with n, n+1 both powerful and
  neither a square.)

  This file formalizes that complete answer as
      ∃ n : Nat, 0 < n ∧ Powerful' n ∧ Powerful' (n+1)
                     ∧ ¬ IsSquare' n ∧ ¬ IsSquare' (n+1)
  with witness n = 12167.

  Definitions (bounded, decidable, equivalent to the standard ones):
  - `Prime' p`: p ≥ 2 and every divisor m of p with m < p+1 is 1 or p.
    (Every divisor m of p satisfies m ≤ p < p+1, so this is exactly primality.)
  - `IsSquare' n`: n = r*r for some r < n+1.
    (A square root r of n ≥ 1 satisfies r ≤ n < n+1, so this is exactly
    "n is a square".)
  - `Powerful' n`: p^2 ∣ n for every prime p ∣ n — the standard definition
    ("every prime occurs with exponent at least two").

  The finite divisor/square checks are carried out by `native_decide`
  (kernel `decide` on these ~12k-case statements exceeds the available
  per-process recursion/memory budget; `native_decide` evaluates the same
  decidable propositions via compiled code in a few seconds each).
  This introduces Lean-generated `..._native.native_decide.ax_1_1` axioms
  (see `#print axioms` below) — disclosed here, not hidden. They are not
  `sorryAx`: each asserts that the native evaluation of the stated decidable
  proposition returned `true`.

  Lean core only (no Mathlib, no imports). No `sorry`/`admit`.
-/

/-- Primality in bounded, decidable form. -/
abbrev Prime' (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ m : Fin (p + 1), m.val ∣ p → m.val = 1 ∨ m.val = p

/-- "n is a square" in bounded, decidable form. -/
abbrev IsSquare' (n : Nat) : Prop :=
  ∃ r : Fin (n + 1), n = r.val * r.val

/-- n is powerful: every prime divisor occurs with exponent at least two. -/
abbrev Powerful' (n : Nat) : Prop :=
  ∀ p : Nat, Prime' p → p ∣ n → p ^ 2 ∣ n

/-! ## Divisor classifications (by native_decide) -/

set_option maxRecDepth 100000 in
/-- Every divisor of 12167 below 12168 is 1, 23, or composite. -/
theorem divs_12167 (p : Nat) (hle : p < 12168) (hpdvd : p ∣ 12167) :
    p = 1 ∨ p = 23 ∨ (∃ m : Fin p, 2 ≤ m.val ∧ m.val ∣ p ∧ m.val ≠ p) := by
  have key : ∀ q : Fin 12168, q.val ∣ 12167 →
      q.val = 1 ∨ q.val = 23 ∨
      (∃ m : Fin q.val, 2 ≤ m.val ∧ m.val ∣ q.val ∧ m.val ≠ q.val) := by
    native_decide
  simpa using key ⟨p, hle⟩ hpdvd

set_option maxRecDepth 100000 in
/-- Every divisor of 12168 below 12169 is 1, 2, 3, 13, or composite. -/
theorem divs_12168 (p : Nat) (hle : p < 12169) (hpdvd : p ∣ 12168) :
    p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 13 ∨
    (∃ m : Fin p, 2 ≤ m.val ∧ m.val ∣ p ∧ m.val ≠ p) := by
  have key : ∀ q : Fin 12169, q.val ∣ 12168 →
      q.val = 1 ∨ q.val = 2 ∨ q.val = 3 ∨ q.val = 13 ∨
      (∃ m : Fin q.val, 2 ≤ m.val ∧ m.val ∣ q.val ∧ m.val ≠ q.val) := by
    native_decide
  simpa using key ⟨p, hle⟩ hpdvd

/-! ## 12167 is powerful -/

/-- 12167 is powerful: its only prime divisor is 23, and 23^2 ∣ 12167. -/
theorem powerful_12167 : Powerful' 12167 := by
  intro p hp hpdvd
  have hle : p < 12168 :=
    Nat.lt_of_le_of_lt (Nat.le_of_dvd (by decide) hpdvd) (by decide)
  rcases divs_12167 p hle hpdvd with rfl | rfl | ⟨m, hm2, hmdvd, hmne⟩
  · exact absurd hp.1 (by decide)
  · exact ⟨23, by decide⟩
  · exfalso
    have h1 : m.val < p + 1 := by
      have hlt := m.isLt
      omega
    rcases hp.2 ⟨m.val, h1⟩ hmdvd with h | h
    · change m.val = 1 at h
      omega
    · change m.val = p at h
      exact hmne h

/-! ## 12168 is powerful -/

/-- 12168 is powerful: its prime divisors are exactly 2, 3, 13, and
    2^2, 3^2, 13^2 each divide 12168. -/
theorem powerful_12168 : Powerful' 12168 := by
  intro p hp hpdvd
  have hle : p < 12169 :=
    Nat.lt_of_le_of_lt (Nat.le_of_dvd (by decide) hpdvd) (by decide)
  rcases divs_12168 p hle hpdvd with rfl | rfl | rfl | rfl | ⟨m, hm2, hmdvd, hmne⟩
  · exact absurd hp.1 (by decide)
  · decide
  · decide
  · decide
  · exfalso
    have h1 : m.val < p + 1 := by
      have hlt := m.isLt
      omega
    rcases hp.2 ⟨m.val, h1⟩ hmdvd with h | h
    · change m.val = 1 at h
      omega
    · change m.val = p at h
      exact hmne h

/-! ## Neither is a square -/

set_option maxRecDepth 100000 in
/-- 12167 is not a square (110^2 = 12100 < 12167 < 12321 = 111^2). -/
theorem not_isSquare_12167 : ¬ IsSquare' 12167 := by
  native_decide

set_option maxRecDepth 100000 in
/-- 12168 is not a square (110^2 = 12100 < 12168 < 12321 = 111^2). -/
theorem not_isSquare_12168 : ¬ IsSquare' 12168 := by
  native_decide

/-! ## Main theorem -/

/-- Golomb's answer to JSP-000301: 12167 and 12168 are consecutive powerful
    numbers, neither of which is a square. -/
theorem jsp000301 :
    ∃ n : Nat, 0 < n ∧ Powerful' n ∧ Powerful' (n + 1) ∧
      ¬ IsSquare' n ∧ ¬ IsSquare' (n + 1) := by
  have h : (12167 + 1) = 12168 := rfl
  refine ⟨12167, by decide, powerful_12167, ?_, not_isSquare_12167, ?_⟩
  · rw [h]; exact powerful_12168
  · rw [h]; exact not_isSquare_12168

-- Axiom audit (disclosed: the native_decide axioms below are Lean-generated,
-- not sorryAx; see the header comment).
#print axioms jsp000301
#print axioms powerful_12167
#print axioms powerful_12168
#print axioms not_isSquare_12167
#print axioms not_isSquare_12168
