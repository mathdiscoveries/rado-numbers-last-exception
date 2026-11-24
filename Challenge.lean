module

/-!
# Palomar Challenge: The Last Exception for Two-Colour Rado Numbers (`x + y + c = k z`)

Self-contained pure core Lean 4 statements (zero external dependencies, zero Mathlib
imports, zero `sorry` in `Solution`, zero `native_decide`, standard axioms only)
determining the exact last exception `c*(k)` and threshold `ν(k)` for the 2-colour
Rado number `R(c, k)` of the linear equation `x + y + c = k z` for every `k ≥ 3`.

Definitions (following Martinelli and Schaal 2007; Kim, Song, and Hwang 2023):
* `LB c k = ⌈(2 ⌈(c + 2)/k⌉ + c)/k⌉`: the Martinelli–Schaal lower bound.
* `cstar k = k(k² + k - 4)/2` for odd `k`, and `k(k² - 2)/2` for even `k`.
* `Valid c k`: `k` is odd or `c` is even (necessary for `R(c, k)` to be finite).
* `HasMono c k n col`: `col : Nat → Bool` has a monochromatic solution of
  `x + y + c = k z` in `[1, n]³`.
* `Forced c k n`: every 2-colouring of `[1, n]` has a monochromatic solution.
* `IsRado c k R`: `R` is the least `n` with `Forced c k n`.

Main theorems compared by Palomar:
1. `rado_last_exception`: Unconditional both-halves characterization written out in
   explicit quantifiers for every `k ≥ 3`.
2. `rado_eq_LB`: Upper half — `R(c, k) = LB(c, k)` for every `k ≥ 3` and every valid
   `c > c*(k)`.
3. `not_forced_cstar`: Boundary colouring — `c*(k)` is an exception:
   `[1, LB(c*(k), k)]` admits a 2-colouring with no monochromatic solution.
4. `nu_iff`: Exact threshold equivalence over all natural-number cutoffs `v` —
   `R(c, k) = LB(c, k)` holds for all valid `c ≥ v` if and only if `c*(k) < v`.
   Thus the least integer cutoff is `c*(k) + 1`, while the least *valid* cutoff `ν(k)`
   (requiring `Valid (ν(k)) k`, i.e., even for even `k`) is `c*(k) + 1` for odd `k`
   and `c*(k) + 2` for even `k`.
5. `nu_5_eq_66`: Settlement of the Kim–Song–Hwang (2023) conjecture `ν(5) = 66`.
6. `nu_small_values`: Exact least valid cutoffs `ν(k) = 13, 30, 66, 104, 183, 250, 388, 492`
   for `k = 3..10`.
-/

@[expose] public section

namespace RadoNuChallenge

/-- Martinelli–Schaal lower bound `LB(c, k) = ceil((2 ceil((c + 2)/k) + c)/k)`. -/
def LB (c k : Nat) : Nat := (2 * ((c + 2 + k - 1) / k) + c + k - 1) / k

/-- Exact last exception `c*(k)`: `k(k^2 + k - 4)/2` for odd `k`, `k(k^2 - 2)/2` for even `k`. -/
def cstar (k : Nat) : Nat :=
  if k % 2 = 1 then k * (k * k + k - 4) / 2 else k * (k * k - 2) / 2

/-- `col` has a monochromatic solution of `x + y + c = k z` in `[1, n]^3`. -/
def HasMono (c k n : Nat) (col : Nat → Bool) : Prop :=
  ∃ x y z : Nat, (1 ≤ x ∧ x ≤ n) ∧ (1 ≤ y ∧ y ≤ n) ∧ (1 ≤ z ∧ z ≤ n) ∧
    x + y + c = k * z ∧ col x = col y ∧ col y = col z

/-- Every 2-colouring of `[1, n]` has a monochromatic solution of `x + y + c = k z`. -/
def Forced (c k n : Nat) : Prop := ∀ col : Nat → Bool, HasMono c k n col

/-- `R` is the 2-colour Rado number `R(c, k)`: the least `n` with `Forced c k n`. -/
def IsRado (c k R : Nat) : Prop := Forced c k R ∧ ∀ n, n < R → ¬ Forced c k n

/-- `c` is valid for `k`: `k` is odd or `c` is even. -/
def Valid (c k : Nat) : Prop := k % 2 = 1 ∨ c % 2 = 0

/-- Complete unconditional both-halves characterization for every `k ≥ 3`, with all
quantifiers expanded explicitly. -/
theorem rado_last_exception (k : Nat) (hk : 3 ≤ k) :
    (∀ c : Nat, cstar k < c → (k % 2 = 1 ∨ c % 2 = 0) →
      (∀ col : Nat → Bool, ∃ x y z : Nat,
        (1 ≤ x ∧ x ≤ LB c k) ∧ (1 ≤ y ∧ y ≤ LB c k) ∧ (1 ≤ z ∧ z ≤ LB c k) ∧
        x + y + c = k * z ∧ col x = col y ∧ col y = col z) ∧
      (∃ col : Nat → Bool, ∀ x y z : Nat,
        1 ≤ x → x < LB c k → 1 ≤ y → y < LB c k → 1 ≤ z → z < LB c k →
        x + y + c = k * z → ¬ (col x = col y ∧ col y = col z))) ∧
    (∃ col : Nat → Bool, ∀ x y z : Nat,
      1 ≤ x → x ≤ LB (cstar k) k →
      1 ≤ y → y ≤ LB (cstar k) k →
      1 ≤ z → z ≤ LB (cstar k) k →
      x + y + cstar k = k * z →
      ¬ (col x = col y ∧ col y = col z)) := by
  sorry

/-- Upper half: `R(c, k) = LB(c, k)` for every `k ≥ 3` and every valid `c > c*(k)`. -/
theorem rado_eq_LB {k c : Nat} (hk : 3 ≤ k) (hc : cstar k < c)
    (hval : Valid c k) : IsRado c k (LB c k) := by
  sorry

/-- Boundary colouring: `[1, LB(c*(k), k)]` is not forced
for `x + y + c*(k) = k z` (some 2-colouring has no monochromatic solution, so `c*(k)`
is an exception to `R(c, k) = LB(c, k)`). -/
theorem not_forced_cstar {k : Nat} (hk : 3 ≤ k) :
    ¬ Forced (cstar k) k (LB (cstar k) k) := by
  sorry

/-- Exact threshold characterization over all natural-number cutoffs `v`:
`R(c, k) = LB(c, k)` for all valid `c ≥ v` if and only if `c*(k) < v`.
Hence the least integer cutoff is `c*(k) + 1`, while the least valid cutoff `ν(k)`
(requiring `Valid (ν(k)) k`) is `c*(k) + 1` for odd `k` and `c*(k) + 2` for even `k`. -/
theorem nu_iff (k : Nat) (hk : 3 ≤ k) (v : Nat) :
    (∀ c, v ≤ c → Valid c k → IsRado c k (LB c k)) ↔ cstar k < v := by
  sorry

/-- Settlement of the Kim–Song–Hwang (2023) conjecture `ν(5) = 66`. -/
theorem nu_5_eq_66 :
    (∀ c, 66 ≤ c → Valid c 5 → IsRado c 5 (LB c 5)) ∧
    ¬ (∀ c, 65 ≤ c → Valid c 5 → IsRado c 5 (LB c 5)) := by
  sorry

/-- Exact least valid cutoffs `ν(k) = c*(k) + 1` (odd `k`), `c*(k) + 2` (even `k`)
for `k = 3..10`. -/
theorem nu_small_values :
    cstar 3 + 1 = 13 ∧ cstar 4 + 2 = 30 ∧ cstar 5 + 1 = 66 ∧
    cstar 6 + 2 = 104 ∧ cstar 7 + 1 = 183 ∧ cstar 8 + 2 = 250 ∧
    cstar 9 + 1 = 388 ∧ cstar 10 + 2 = 492 := by
  sorry

end RadoNuChallenge
