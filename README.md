# JSP-000301 — Lean 4 Formalization

Formalization of the disproof of Golomb's question
([JSP-000301](https://github.com/TheJustinSunPrize/awards)):

> If two consecutive positive integers are powerful, must at least one be a perfect square?

**Answer: No.** Counterexample: `12167 = 23³` and `12168 = 2³ · 3² · 13²`.
Both are powerful (every prime exponent ≥ 2) and neither is a square
(`110² = 12100 < 12167 < 12168 < 12321 = 111²`).

## Main theorem

```lean
theorem jsp000301 :
    ∃ n : Nat, 0 < n ∧ Powerful' n ∧ Powerful' (n + 1) ∧
      ¬ IsSquare' n ∧ ¬ IsSquare' (n + 1)
```

where `Powerful'` and `IsSquare'` are the bounded, decidable forms of the
standard definitions: `Powerful' n := ∀ p : Nat, Prime' p → p ∣ n → p ^ 2 ∣ n`
(every prime divisor occurs with exponent ≥ 2) and
`IsSquare' n := ∃ r : Fin (n + 1), n = r.val * r.val`.

File: `JSP000301.lean` (root of the `JSP000301` library).

## Build

Requires Lean 4.34.1 (see `lean-toolchain`). Core only — no Mathlib, no
`lake update` needed:

```sh
lean JSP000301.lean
```

Compiles cleanly (exit 0, no errors, no `sorry`/`admit`).

## Axiom audit

```sh
lean JSP000301.lean   # the file ends with #print axioms lines
```

Actual output (verified 2026-10-09 with Lean 4.34.1):

```
'jsp000301' depends on axioms: [propext, Quot.sound,
  divs_12167._native.native_decide.ax_1_1,
  divs_12168._native.native_decide.ax_1_1,
  not_isSquare_12167._native.native_decide.ax_1_1,
  not_isSquare_12168._native.native_decide.ax_1_1]
```

The four `native_decide` axioms are Lean-generated (not `sorryAx`): each
asserts that native evaluation of the stated decidable proposition returned
`true`. The finite divisor/square classifications they certify are
independently re-checkable in Python (see the header comment in the file).
No `sorry` or `admit` is used anywhere in the proof.

## Mathematical source

- S. W. Golomb, "Powerful numbers", *Amer. Math. Monthly* 77(8) (1970), 848–852.
- Erdős problem [#365](https://www.erdosproblems.com/365).
- The catalog record for JSP-000301 documents the disproof with the factorizations above.
