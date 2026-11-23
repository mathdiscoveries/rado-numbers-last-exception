module

public import RadoNu

/-!
# Palomar Solution: The Last Exception for Two-Colour Rado Numbers (`x + y + c = k z`)
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
      ¬ (col x = col y ∧ col y = col z)) :=
  RadoNu.R17_3_1 k hk

theorem rado_eq_LB {k c : Nat} (hk : 3 ≤ k) (hc : cstar k < c)
    (hval : Valid c k) : IsRado c k (LB c k) :=
  RadoNu.rado_eq_LB hk hc hval

theorem not_forced_cstar {k : Nat} (hk : 3 ≤ k) :
    ¬ Forced (cstar k) k (LB (cstar k) k) :=
  RadoNu.not_forced_cstar hk

theorem nu_iff (k : Nat) (hk : 3 ≤ k) (v : Nat) :
    (∀ c, v ≤ c → Valid c k → IsRado c k (LB c k)) ↔ cstar k < v :=
  RadoNu.nu_iff k hk v

theorem nu_5_eq_66 :
    (∀ c, 66 ≤ c → Valid c 5 → IsRado c 5 (LB c 5)) ∧
    ¬ (∀ c, 65 ≤ c → Valid c 5 → IsRado c 5 (LB c 5)) :=
  RadoNu.nu_5_eq_66

theorem nu_small_values :
    cstar 3 + 1 = 13 ∧ cstar 4 + 2 = 30 ∧ cstar 5 + 1 = 66 ∧
    cstar 6 + 2 = 104 ∧ cstar 7 + 1 = 183 ∧ cstar 8 + 2 = 250 ∧
    cstar 9 + 1 = 388 ∧ cstar 10 + 2 = 492 :=
  RadoNu.nu_small_values

end RadoNuChallenge
