module

/-!
# `RadoNu`: Exact Two-Colour Rado Last Exception `ν(k)` for All `k ≥ 3`

Port of `docs/shadow/round18/R18-5/R17_3_1.lean` (core Lean 4.35.0, no Mathlib
imports) into the unified `lean/` factory.

Source of the proof: `docs/shadow/round17/R17-3/candidates.json` (`R17-3-1`) and
`theorem_R17-3-1.md`, sections 2 to 5, read line by line in
`docs/shadow/round17/R17-3/falsify/verdict.md` and `review/review.md`.

Definitions (Kim, Song and Hwang, *Discrete Math.* 346 (2023) 113597):
* `R(c, k)`: the least `R` such that every 2-colouring of `[1, R]` has a
  monochromatic solution of `x + y + c = k z`.
* `LB(c, k) = ceil((2 ceil((c + 2)/k) + c)/k)`.
* `c*(k) = k(k^2 + k - 4)/2` for odd `k`, `k(k^2 - 2)/2` for even `k`.
* `c` is valid for `k` when `k` is odd or `c` is even.

`R17-3-1`: for every `k >= 3`, `R(c, k) = LB(c, k)` for every valid `c > c*(k)`,
and `R(c*(k), k) > LB(c*(k), k)`.

Layout:
* `namespace T2`: the lower half, `R(c*(k), k) > LB(c*(k), k)` (ported verbatim
  from `docs/shadow/round17/R17-5/T2.lean` / `docs/shadow/round18/R18-5/R17_3_1.lean`).
* Part A: the reflected equation `x + y = k z + b`, the forcing rule, Lemmas 0, S, E, F.
* Part B: Theorem 1 (`b >= k + 1`) and Theorem 2 (`1 <= b <= k`).
* Part C: Lemma A, the reflection `x -> N + 1 - x`, the upper bound
  `R(c, k) <= LB(c, k)`, Martinelli and Schaal's lower bound `R(c, k) >= LB(c, k)`,
  and the main theorems (`R17_3_1`, `R17_3_1_rado`, `nu_iff`).

All `#print axioms` checks live in `RadoNu/Verify.lean`.
-/

@[expose] public section

namespace RadoNu

/-! # The lower half: T2 (round 17, R17-5), definitions and proof unchanged -/

namespace T2

/-! ## Definitions, as in the text -/

/-- LB(c, k) = ceil((2 ceil((c + 2)/k) + c)/k); `ceil(a/k)` is `(a + k - 1) / k`. -/
def LB (c k : Nat) : Nat := (2 * ((c + 2 + k - 1) / k) + c + k - 1) / k

/-- c*(k) = k(k^2 + k - 4)/2 for odd k, k(k^2 - 2)/2 for even k. -/
def cstar (k : Nat) : Nat :=
  if k % 2 = 1 then k * (k * k + k - 4) / 2 else k * (k * k - 2) / 2

/-- Odd k = 2j + 1, so j = (k - 1)/2: colour 1 if x mod k is in [1, j], or if
k | x and x >= k(floor(j/2) + 2); colour 0 otherwise. -/
def colOdd (k x : Nat) : Bool :=
  decide ((1 ≤ x % k ∧ x % k ≤ (k - 1) / 2) ∨
    (x % k = 0 ∧ k * ((k - 1) / 2 / 2 + 2) ≤ x))

/-- Even k, q = k(k - 2)/2: colour 0 on {q + 1} and [q + k, q + 2k - 2],
colour 1 elsewhere. -/
def colEven (k x : Nat) : Bool :=
  decide (¬ (x = k * (k - 2) / 2 + 1 ∨
    (k * (k - 2) / 2 + k ≤ x ∧ x ≤ k * (k - 2) / 2 + 2 * k - 2)))

/-- The proof's colouring for k. -/
def col (k x : Nat) : Bool := if k % 2 = 1 then colOdd k x else colEven k x

/-- The proof's N: k(j + 2) - 1 for odd k = 2j + 1; q + 2k - 1 for even k. -/
def N (k : Nat) : Nat :=
  if k % 2 = 1 then k * ((k - 1) / 2 + 2) - 1 else k * (k - 2) / 2 + 2 * k - 1

/-! ## Small arithmetic lemmas -/

theorem div_eq_of_decomp {a k q r : Nat} (h : a = k * q + r) (hr : r < k) :
    a / k = q := by
  subst h
  rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, Nat.add_zero]

theorem mod_eq_of_decomp {a k q r : Nat} (h : a = k * q + r) (hr : r < k) :
    a % k = r := by
  subst h
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/-- If r + s = k w with r, s < k then w <= 1. -/
theorem sum_lt_two {k r s w : Nat} (hr : r < k) (hs : s < k)
    (h : r + s = k * w) : w = 0 ∨ w = 1 := by
  by_cases hw : 2 ≤ w
  · have h2 := Nat.mul_le_mul_left k hw
    omega
  · omega

/-- From x + y + k m = k z: z = m + t with x + y = k t. -/
theorem shift {k m x y z : Nat} (hk : 0 < k) (h : x + y + k * m = k * z) :
    ∃ t, z = m + t ∧ x + y = k * t := by
  have hzm : m ≤ z := by
    by_cases hc : m ≤ z
    · exact hc
    · have h1 := Nat.mul_le_mul_left k (show z + 1 ≤ m by omega)
      have h2 := Nat.mul_add k z 1
      omega
  refine ⟨z - m, by omega, ?_⟩
  have h3 := Nat.mul_add k m (z - m)
  rw [show m + (z - m) = z by omega] at h3
  omega

/-! ## Odd k = 2j + 1 -/

theorem sq_odd {k j : Nat} (hk : k = 2 * j + 1) : k * k = 2 * (k * j) + k := by
  have h1 : k * k = k * (2 * j + 1) := by rw [← hk]
  rw [h1, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]

/-- c*(k) = k m with m = k j + 2j - 1 (= (k^2 + k - 4)/2). -/
theorem cstar_odd {k j : Nat} (hk : k = 2 * j + 1) (hj : 1 ≤ j) :
    cstar k = k * (k * j + 2 * j - 1) := by
  have hkk := sq_odd hk
  have hmod : k % 2 = 1 := by omega
  have h2 : k * k + k - 4 = 2 * (k * j + 2 * j - 1) := by omega
  unfold cstar
  simp only [hmod, ↓reduceIte]
  rw [h2, Nat.mul_left_comm k 2, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

/-- LB(c*(k), k) = k(j + 2) - 1 for odd k = 2j + 1. -/
theorem LB_odd {k j : Nat} (hk : k = 2 * j + 1) (hj : 1 ≤ j) :
    LB (cstar k) k = k * (j + 2) - 1 := by
  have hkk := sq_odd hk
  rw [cstar_odd hk hj]
  obtain ⟨m, hm⟩ : ∃ m, m = k * j + 2 * j - 1 := ⟨_, rfl⟩
  rw [← hm]
  have e1 := Nat.mul_add k m 1
  have e2 := Nat.mul_add k m (k + 1)
  have e3 := Nat.mul_add k k 1
  have e4 := Nat.mul_add k j 2
  have h1 : (k * m + 2 + k - 1) / k = m + 1 :=
    div_eq_of_decomp (r := 1) (by omega) (by omega)
  have h2 : (2 * (m + 1) + k * m + k - 1) / k = m + (k + 1) :=
    div_eq_of_decomp (r := k - 3) (by omega) (by omega)
  unfold LB
  rw [h1, h2]
  omega

/-- The odd colouring at x = k u + r, r < k. -/
theorem colOdd_eq {k j u r : Nat} (hk : k = 2 * j + 1) (hr : r < k) :
    colOdd k (k * u + r) =
      decide ((1 ≤ r ∧ r ≤ j) ∨ (r = 0 ∧ j / 2 + 2 ≤ u)) := by
  have hmod : (k * u + r) % k = r := mod_eq_of_decomp rfl hr
  have hj : (k - 1) / 2 = j := by omega
  unfold colOdd
  rw [hmod, hj]
  apply decide_eq_decide.mpr
  by_cases hu : j / 2 + 2 ≤ u
  · have h1 := Nat.mul_le_mul_left k hu
    omega
  · have h1 := Nat.mul_le_mul_left k (show u + 1 ≤ j / 2 + 2 by omega)
    have h2 := Nat.mul_add k u 1
    omega

/-- Odd case of T2, with N and c* in the proof's closed forms. -/
theorem odd_case {k j : Nat} (hk : k = 2 * j + 1) (hj : 1 ≤ j) (x y z : Nat)
    (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) (hzN : z ≤ k * (j + 2) - 1)
    (h : x + y + k * (k * j + 2 * j - 1) = k * z) :
    ¬ (colOdd k x = colOdd k y ∧ colOdd k y = colOdd k z) := by
  have hkpos : 0 < k := by omega
  obtain ⟨m, hm⟩ : ∃ m, m = k * j + 2 * j - 1 := ⟨_, rfl⟩
  rw [← hm] at h
  obtain ⟨t, rfl, hxy⟩ := shift hkpos h
  have e1 := Nat.mul_add k j 2
  have e2 := Nat.mul_add k j 1
  have ht : t ≤ k + 1 := by omega
  -- x = k u + r, y = k v + s
  obtain ⟨u, r, hr, rfl⟩ : ∃ u r, r < k ∧ x = k * u + r :=
    ⟨x / k, x % k, Nat.mod_lt x hkpos, (Nat.div_add_mod x k).symm⟩
  obtain ⟨v, s, hs, rfl⟩ : ∃ v s, s < k ∧ y = k * v + s :=
    ⟨y / k, y % k, Nat.mod_lt y hkpos, (Nat.div_add_mod y k).symm⟩
  have e3 := Nat.mul_add k u v
  have huv : u + v ≤ t := by
    by_cases hc : u + v ≤ t
    · exact hc
    · have h1 := Nat.mul_le_mul_left k (show t + 1 ≤ u + v by omega)
      have h2 := Nat.mul_add k t 1
      omega
  obtain ⟨w, rfl⟩ : ∃ w, t = u + v + w := ⟨t - (u + v), by omega⟩
  have e4 := Nat.mul_add k (u + v) w
  have hrs : r + s = k * w := by omega
  intro ⟨h1, h2⟩
  rw [colOdd_eq hk hr, colOdd_eq hk hs] at h1
  have a := decide_eq_decide.mp h1
  rcases sum_lt_two hr hs hrs with hw | hw
  · -- r = s = 0: x = k u, y = k v, t = u + v
    subst hw
    have hr0 : r = 0 := by omega
    have hs0 : s = 0 := by omega
    have hu : 1 ≤ u := by
      rcases Nat.eq_zero_or_pos u with h0 | h0
      · subst h0; omega
      · exact h0
    have hv : 1 ≤ v := by
      rcases Nat.eq_zero_or_pos v with h0 | h0
      · subst h0; omega
      · exact h0
    -- z = m + t = k (j + 1) + (t - 2), residue t - 2 < k
    have hz : m + (u + v + 0) = k * (j + 1) + (u + v - 2) := by omega
    rw [colOdd_eq hk hs, hz, colOdd_eq hk (show u + v - 2 < k by omega)] at h2
    have b := decide_eq_decide.mp h2
    omega
  · -- r + s = k: residues r and k - r take different colours
    subst hw
    omega

/-! ## Even k = 2j, j >= 2 -/

theorem sq_even {k j : Nat} (hk : k = 2 * j) : k * k = 2 * (k * j) := by
  have h1 : k * k = k * (2 * j) := by rw [← hk]
  rw [h1, Nat.mul_left_comm]

theorem mul_pred {k j : Nat} (hj : 2 ≤ j) : k * j = k * (j - 1) + k := by
  have h := Nat.mul_add k (j - 1) 1
  rw [show j - 1 + 1 = j by omega, Nat.mul_one] at h
  exact h

/-- q = k(k - 2)/2 = k(j - 1). -/
theorem q_even {k j : Nat} (hk : k = 2 * j) (hj : 2 ≤ j) :
    k * (k - 2) / 2 = k * (j - 1) := by
  rw [show k - 2 = 2 * (j - 1) by omega, Nat.mul_left_comm k 2,
    Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

/-- c*(k) = k m with m = k j - 1 (= (k^2 - 2)/2). -/
theorem cstar_even {k j : Nat} (hk : k = 2 * j) (hj : 2 ≤ j) :
    cstar k = k * (k * j - 1) := by
  have hkk := sq_even hk
  have hpos := Nat.mul_le_mul_left k hj
  have hmod : ¬ k % 2 = 1 := by omega
  have h2 : k * k - 2 = 2 * (k * j - 1) := by omega
  unfold cstar
  simp only [hmod, ↓reduceIte]
  rw [h2, Nat.mul_left_comm k 2, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

/-- LB(c*(k), k) = q + 2k - 1 for even k >= 4. -/
theorem LB_even {k j : Nat} (hk : k = 2 * j) (hj : 2 ≤ j) :
    LB (cstar k) k = k * (k - 2) / 2 + 2 * k - 1 := by
  have hq := q_even hk hj
  have hkj := mul_pred (k := k) hj
  have hkk := sq_even hk
  rw [cstar_even hk hj, hq]
  obtain ⟨m, hm⟩ : ∃ m, m = k * j - 1 := ⟨_, rfl⟩
  rw [← hm]
  have e1 := Nat.mul_add k m 1
  have e2 := Nat.mul_add k m k
  have h1 : (k * m + 2 + k - 1) / k = m + 1 :=
    div_eq_of_decomp (r := 1) (by omega) (by omega)
  have h2 : (2 * (m + 1) + k * m + k - 1) / k = m + k :=
    div_eq_of_decomp (r := k - 1) (by omega) (by omega)
  unfold LB
  rw [h1, h2]
  omega

/-- Even case of T2, with N and c* in the proof's closed forms. -/
theorem even_case {k j : Nat} (hk : k = 2 * j) (hj : 2 ≤ j) (x y z : Nat)
    (hx1 : 1 ≤ x) (hxN : x ≤ k * (k - 2) / 2 + 2 * k - 1)
    (hy1 : 1 ≤ y) (hyN : y ≤ k * (k - 2) / 2 + 2 * k - 1)
    (hzN : z ≤ k * (k - 2) / 2 + 2 * k - 1)
    (h : x + y + k * (k * j - 1) = k * z) :
    ¬ (colEven k x = colEven k y ∧ colEven k y = colEven k z) := by
  have hkpos : 0 < k := by omega
  have hq := q_even hk hj
  have hkj := mul_pred (k := k) hj
  have hkk := sq_even hk
  have hc : ∀ n, colEven k n = decide (¬ (n = k * (j - 1) + 1 ∨
      (k * (j - 1) + k ≤ n ∧ n ≤ k * (j - 1) + 2 * k - 2))) := by
    intro n
    unfold colEven
    rw [hq]
  rw [hq] at hxN hyN hzN
  rw [hc x, hc y, hc z]
  obtain ⟨m, hm⟩ : ∃ m, m = k * j - 1 := ⟨_, rfl⟩
  rw [← hm] at h
  obtain ⟨t, rfl, hxy⟩ := shift hkpos h
  have ht : t ≤ k := by omega
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0; omega
    · exact h0
  intro ⟨h1, h2⟩
  have a := decide_eq_decide.mp h1
  have b := decide_eq_decide.mp h2
  by_cases htk : t = k
  · -- z = N has colour 1; x + y = k^2
    rw [htk] at hxy
    omega
  · by_cases ht2 : t ≤ k - 2
    · -- x + y <= k(k - 2) = 2q
      have h3 := Nat.mul_le_mul_left k ht2
      have h4 : k * (k - 2) = 2 * (k * (j - 1)) := by
        rw [show k - 2 = 2 * (j - 1) by omega, Nat.mul_left_comm]
      omega
    · -- t = k - 1: x + y = k(k - 1) = 2q + k
      have h3 : t = k - 1 := by omega
      have h4 := Nat.mul_add k (k - 1) 1
      rw [show k - 1 + 1 = k by omega] at h4
      rw [h3] at hxy
      omega

/-! ## The claim -/

/-- LB(c*(k), k) equals the proof's N, for every k >= 3. -/
theorem LB_cstar (k : Nat) (hk : 3 ≤ k) : LB (cstar k) k = N k := by
  unfold N
  by_cases hodd : k % 2 = 1
  · simp only [hodd, ↓reduceIte]
    exact LB_odd (by omega) (by omega)
  · simp only [hodd, ↓reduceIte]
    exact LB_even (j := k / 2) (by omega) (by omega)

/-- The proof's colouring `col k` has no monochromatic solution on
[1, LB(c*(k), k)]. -/
theorem T2_col (k : Nat) (hk : 3 ≤ k) (x y z : Nat)
    (hx1 : 1 ≤ x) (hxN : x ≤ LB (cstar k) k)
    (hy1 : 1 ≤ y) (hyN : y ≤ LB (cstar k) k)
    (_hz1 : 1 ≤ z) (hzN : z ≤ LB (cstar k) k)
    (h : x + y + cstar k = k * z) :
    ¬ (col k x = col k y ∧ col k y = col k z) := by
  by_cases hodd : k % 2 = 1
  · have hkj : k = 2 * (k / 2) + 1 := by omega
    have hj : 1 ≤ k / 2 := by omega
    rw [LB_odd hkj hj] at hzN
    rw [cstar_odd hkj hj] at h
    have hc : ∀ n, col k n = colOdd k n := fun n => by
      simp only [col, hodd, ↓reduceIte]
    rw [hc x, hc y, hc z]
    exact odd_case hkj hj x y z hx1 hy1 hzN h
  · have hkj : k = 2 * (k / 2) := by omega
    have hj : 2 ≤ k / 2 := by omega
    rw [LB_even hkj hj] at hxN hyN hzN
    rw [cstar_even hkj hj] at h
    have hc : ∀ n, col k n = colEven k n := fun n => by
      simp only [col, hodd, ↓reduceIte]
    rw [hc x, hc y, hc z]
    exact even_case hkj hj x y z hx1 hxN hy1 hyN hzN h

/-- **T2.** For every k >= 3, some 2-colouring of [1, LB(c*(k), k)] has no
monochromatic solution of x + y + c*(k) = k z; so R(c*(k), k) > LB(c*(k), k). -/
theorem T2 (k : Nat) (hk : 3 ≤ k) :
    ∃ col : Nat → Bool, ∀ x y z : Nat,
      1 ≤ x → x ≤ LB (cstar k) k →
      1 ≤ y → y ≤ LB (cstar k) k →
      1 ≤ z → z ≤ LB (cstar k) k →
      x + y + cstar k = k * z →
      ¬ (col x = col y ∧ col y = col z) :=
  ⟨col k, fun x y z hx1 hxN hy1 hyN hz1 hzN h =>
    T2_col k hk x y z hx1 hxN hy1 hyN hz1 hzN h⟩

end T2

/-! # The upper half and the theorem -/

open T2 (LB cstar)

/-! ## Part A: the reflected equation x + y = k z + b; the forcing rule;
Lemmas 0, S, E, F (theorem_R17-3-1.md, sections 2 and 3)

In Parts A and B blue is `false` and red is `true`. -/


/-- A colouring of [1, N] is good for x + y = k z + b when no solution in
[1, N]^3 is monochromatic. -/
def Good (k b N : Nat) (col : Nat → Bool) : Prop :=
  ∀ x y z : Nat, 1 ≤ x → x ≤ N → 1 ≤ y → y ≤ N → 1 ≤ z → z ≤ N →
    x + y = k * z + b → ¬ (col x = col y ∧ col y = col z)

/-! ## The forcing rule -/

theorem force_z {k b N : Nat} {col : Nat → Bool} (g : Good k b N col)
    {x y z : Nat} {c : Bool} (hx : 1 ≤ x ∧ x ≤ N) (hy : 1 ≤ y ∧ y ≤ N)
    (hz : 1 ≤ z ∧ z ≤ N) (h : x + y = k * z + b)
    (cx : col x = c) (cy : col y = c) : col z = !c := by
  have h0 := g x y z hx.1 hx.2 hy.1 hy.2 hz.1 hz.2 h
  cases hcz : col z <;> cases c <;> simp_all

theorem force_y {k b N : Nat} {col : Nat → Bool} (g : Good k b N col)
    {x y z : Nat} {c : Bool} (hx : 1 ≤ x ∧ x ≤ N) (hy : 1 ≤ y ∧ y ≤ N)
    (hz : 1 ≤ z ∧ z ≤ N) (h : x + y = k * z + b)
    (cx : col x = c) (cz : col z = c) : col y = !c := by
  have h0 := g x y z hx.1 hx.2 hy.1 hy.2 hz.1 hz.2 h
  cases hcy : col y <;> cases c <;> simp_all

/-- For a solution (x, x, z): the colour of z gives the colour of x. -/
theorem force_xx {k b N : Nat} {col : Nat → Bool} (g : Good k b N col)
    {x z : Nat} {c : Bool} (hx : 1 ≤ x ∧ x ≤ N)
    (hz : 1 ≤ z ∧ z ≤ N) (h : x + x = k * z + b)
    (cz : col z = c) : col x = !c := by
  have h0 := g x x z hx.1 hx.2 hx.1 hx.2 hz.1 hz.2 h
  cases hcx : col x <;> cases c <;> simp_all

/-- Swapping the two colours keeps a colouring good. -/
theorem good_not {k b N : Nat} {col : Nat → Bool} (g : Good k b N col) :
    Good k b N (fun x => !col x) := by
  intro x y z hx1 hxN hy1 hyN hz1 hzN h hm
  apply g x y z hx1 hxN hy1 hyN hz1 hzN h
  cases hx : col x <;> cases hy : col y <;> cases hz : col z <;> simp_all

/-- A colouring that is not good has a monochromatic solution. -/
theorem exists_mono {k b N : Nat} {col : Nat → Bool} (h : ¬ Good k b N col) :
    ∃ x y z : Nat, (1 ≤ x ∧ x ≤ N) ∧ (1 ≤ y ∧ y ≤ N) ∧ (1 ≤ z ∧ z ≤ N) ∧
      x + y = k * z + b ∧ col x = col y ∧ col y = col z :=
  Classical.byContradiction fun hne => h fun x y z hx1 hxN hy1 hyN hz1 hzN e hm =>
    hne ⟨x, y, z, ⟨hx1, hxN⟩, ⟨hy1, hyN⟩, ⟨hz1, hzN⟩, e, hm.1, hm.2⟩

/-! ## The least red number -/

theorem least_true (p : Nat → Bool) : ∀ n, p n = true →
    ∃ t, t ≤ n ∧ p t = true ∧ ∀ x, x < t → p x = false := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases h : ∃ x, x < n ∧ p x = true
    · obtain ⟨x, hx, hpx⟩ := h
      obtain ⟨t, ht, hpt, hmin⟩ := ih x hx hpx
      exact ⟨t, by omega, hpt, hmin⟩
    · refine ⟨n, Nat.le_refl n, hn, fun x hx => ?_⟩
      cases hpx : p x
      · rfl
      · exact absurd ⟨x, hx, hpx⟩ h

/-- The standing hypotheses of section 3: a good colouring of [1, N] for
x + y = k z + b, with [1, t - 1] blue (`false`) and t red (`true`), t >= 2. -/
structure Ctx (k b N t : Nat) (col : Nat → Bool) : Prop where
  hk : 3 ≤ k
  hb : 1 ≤ b
  good : Good k b N col
  ht : 2 ≤ t
  blue : ∀ x, 1 ≤ x → x < t → col x = false
  red : col t = true

/-- **Lemma 0.** If h = ceil((k + b)/2) <= N and 1 is blue, the least red
number t exists and 2 <= t <= h. -/
theorem lemma0 {k b N h : Nat} {col : Nat → Bool} (hk : 3 ≤ k) (hb : 1 ≤ b)
    (g : Good k b N col) (h1 : col 1 = false)
    (hh1 : k + b ≤ 2 * h) (hh2 : 2 * h ≤ k + b + 1) (hN : h ≤ N) :
    ∃ t, t ≤ h ∧ Ctx k b N t col := by
  have hex : ∃ n, n ≤ h ∧ (decide (1 ≤ n) && col n) = true := by
    cases hc : col h
    · refine ⟨k + b - h, by omega, ?_⟩
      have h2 := force_y g (x := h) (y := k + b - h) (z := 1)
        ⟨by omega, hN⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) hc h1
      have h3 : 1 ≤ k + b - h := by omega
      simp [h2, h3]
    · refine ⟨h, Nat.le_refl _, ?_⟩
      have h3 : 1 ≤ h := by omega
      simp [hc, h3]
  obtain ⟨n, hn, hpn⟩ := hex
  obtain ⟨t, htn, hpt, hmin⟩ := least_true (fun n => decide (1 ≤ n) && col n) n hpn
  have hpt' : 1 ≤ t ∧ col t = true := by simpa using hpt
  have hblue : ∀ x, 1 ≤ x → x < t → col x = false := by
    intro x hx1 hxt
    have h4 := hmin x hxt
    cases hcx : col x
    · rfl
    · simp [hcx, hx1] at h4
  have ht2 : 2 ≤ t := by
    rcases Nat.lt_or_ge t 2 with h5 | h5
    · have h6 : t = 1 := by omega
      rw [h6, h1] at hpt'
      exact absurd hpt'.2 (by decide)
    · exact h5
  exact ⟨t, by omega, ⟨hk, hb, g, ht2, hblue, hpt'.2⟩⟩

/-! ## Lemma S (spreading) -/

/-- The diagonal point x_j = (k j + b)/2, used when k j + b is even. -/
def X (k b j : Nat) : Nat := (k * j + b) / 2

/-- For j of the parity of Hs with j <= Hs: k j + b is even, and
1 <= x_j <= N. Here Hs (the text's H*) has k Hs + b even and <= 2N. -/
theorem X_facts {k b N Hs j : Nat} (hHe : (k * Hs + b) % 2 = 0)
    (hHN : k * Hs + b ≤ 2 * N) (hb : 1 ≤ b) (hj : j ≤ Hs)
    (hp : j % 2 = Hs % 2) :
    2 * X k b j = k * j + b ∧ 1 ≤ X k b j ∧ X k b j ≤ N := by
  obtain ⟨d, rfl⟩ : ∃ d, Hs = j + 2 * d := ⟨(Hs - j) / 2, by omega⟩
  have e : k * (j + 2 * d) = k * j + 2 * (k * d) := by
    rw [Nat.mul_add, Nat.mul_left_comm]
  unfold X
  omega

/-- x_i + x_j = k m + b when i + j = 2m. -/
theorem X_sum {k b i j m : Nat} (hi : 2 * X k b i = k * i + b)
    (hj : 2 * X k b j = k * j + b) (hm : i + j = 2 * m) :
    X k b i + X k b j = k * m + b := by
  have e : k * i + k * j = 2 * (k * m) := by
    rw [← Nat.mul_add, hm, Nat.mul_left_comm]
  omega

theorem le_N_of_le_Hs {k b N Hs z : Nat} (hk : 3 ≤ k)
    (hHN : k * Hs + b ≤ 2 * N) (hz : z ≤ Hs) : z ≤ N := by
  have := Nat.mul_le_mul_right Hs hk
  omega

/-- The start of Lemma S: with q the least number >= t of the parity of Hs
(q = t or t + 1), x_{q-2} is red and x_q is blue. -/
theorem lemmaS_start {k b N t Hs : Nat} {col : Nat → Bool} (c : Ctx k b N t col)
    (hHe : (k * Hs + b) % 2 = 0) (hHN : k * Hs + b ≤ 2 * N)
    {q : Nat} (hq : q = t ∨ q = t + 1) (hqp : q % 2 = Hs % 2) (hqH : q ≤ Hs) :
    col (X k b (q - 2)) = true ∧ col (X k b q) = false := by
  have hk := c.hk
  have hb := c.hb
  have ht := c.ht
  have htN : t ≤ N := le_N_of_le_Hs hk hHN (show t ≤ Hs by omega)
  rcases hq with rfl | rfl
  · -- q = t: (x_t, x_t, t), then (x_{t-2}, x_t, t - 1)
    have ft := X_facts hHe hHN hb hqH hqp
    have fa := X_facts hHe hHN hb (j := q - 2) (by omega) (by omega)
    have b1 : col (X k b q) = false :=
      force_xx c.good ⟨ft.2.1, ft.2.2⟩ ⟨by omega, htN⟩
        (X_sum ft.1 ft.1 (by omega)) c.red
    have b2 : col (q - 1) = false := c.blue (q - 1) (by omega) (by omega)
    have b3 : col (X k b (q - 2)) = true :=
      force_y c.good (x := X k b q) (z := q - 1) ⟨ft.2.1, ft.2.2⟩
        ⟨fa.2.1, fa.2.2⟩ ⟨by omega, by omega⟩
        (X_sum ft.1 fa.1 (by omega)) b1 b2
    exact ⟨b3, b1⟩
  · -- q = t + 1: (x_{t-1}, x_{t-1}, t - 1), then (x_{t-1}, x_{t+1}, t)
    have e : t + 1 - 2 = t - 1 := by omega
    rw [e]
    have fq := X_facts hHe hHN hb hqH hqp
    have fa := X_facts hHe hHN hb (j := t - 1) (by omega) (by omega)
    have b2 : col (t - 1) = false := c.blue (t - 1) (by omega) (by omega)
    have b3 : col (X k b (t - 1)) = true :=
      force_xx c.good ⟨fa.2.1, fa.2.2⟩ ⟨by omega, by omega⟩
        (X_sum fa.1 fa.1 (by omega)) b2
    have b1 : col (X k b (t + 1)) = false :=
      force_y c.good (x := X k b (t - 1)) (z := t) ⟨fa.2.1, fa.2.2⟩
        ⟨fq.2.1, fq.2.2⟩ ⟨by omega, htN⟩
        (X_sum fa.1 fq.1 (by omega)) b3 c.red
    exact ⟨b3, b1⟩

/-- If x_i is blue for every i >= t of the parity of Hs up to M <= Hs, then z
is red for t <= z, where z <= M (z of that parity) or z + 1 <= M (else). -/
theorem red_of_blue {k b N t Hs : Nat} {col : Nat → Bool} (c : Ctx k b N t col)
    (hHe : (k * Hs + b) % 2 = 0) (hHN : k * Hs + b ≤ 2 * N)
    {M : Nat} (hM : M ≤ Hs)
    (hB : ∀ i, i % 2 = Hs % 2 → t ≤ i → i ≤ M → col (X k b i) = false)
    {z : Nat} (htz : t ≤ z) (h1 : z % 2 = Hs % 2 → z ≤ M)
    (h2 : ¬ z % 2 = Hs % 2 → z + 1 ≤ M) : col z = true := by
  have hk := c.hk
  have hb := c.hb
  have ht := c.ht
  by_cases hp : z % 2 = Hs % 2
  · -- (x_z, x_z, z)
    have hz := h1 hp
    have f := X_facts hHe hHN hb (j := z) (by omega) hp
    have zN : z ≤ N := le_N_of_le_Hs hk hHN (show z ≤ Hs by omega)
    have bz := hB z hp htz hz
    exact force_z c.good ⟨f.2.1, f.2.2⟩ ⟨f.2.1, f.2.2⟩ ⟨by omega, zN⟩
      (X_sum f.1 f.1 (by omega)) bz bz
  · by_cases hzt : z = t
    · rw [hzt]; exact c.red
    · -- (x_{z-1}, x_{z+1}, z)
      have hz := h2 hp
      have f1 := X_facts hHe hHN hb (j := z - 1) (by omega) (by omega)
      have f2 := X_facts hHe hHN hb (j := z + 1) (by omega) (by omega)
      have zN : z ≤ N := le_N_of_le_Hs hk hHN (show z ≤ Hs by omega)
      have b1 := hB (z - 1) (by omega) (by omega) (by omega)
      have b2 := hB (z + 1) (by omega) (by omega) hz
      exact force_z c.good ⟨f1.2.1, f1.2.2⟩ ⟨f2.2.1, f2.2.2⟩ ⟨by omega, zN⟩
        (X_sum f1.1 f2.1 (by omega)) b1 b2

/-- x_j is blue for every j >= t of the parity of Hs, j <= Hs. -/
theorem lemmaS_blue {k b N t Hs : Nat} {col : Nat → Bool} (c : Ctx k b N t col)
    (hHe : (k * Hs + b) % 2 = 0) (hHN : k * Hs + b ≤ 2 * N) :
    ∀ j, j % 2 = Hs % 2 → t ≤ j → j ≤ Hs → col (X k b j) = false := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro hp htj hjH
    have hk := c.hk
    have hb := c.hb
    have ht := c.ht
    obtain ⟨q, hq, hqp⟩ : ∃ q, (q = t ∨ q = t + 1) ∧ q % 2 = Hs % 2 := by
      by_cases h : t % 2 = Hs % 2
      · exact ⟨t, Or.inl rfl, h⟩
      · exact ⟨t + 1, Or.inr rfl, by omega⟩
    have hqj : q ≤ j := by omega
    have st := lemmaS_start c hHe hHN hq hqp (by omega)
    by_cases hjq : j = q
    · rw [hjq]; exact st.2
    · -- (x_{q-2}, x_j, z) with 2z = j + q - 2, and z is red
      obtain ⟨z, hz⟩ : ∃ z, j + (q - 2) = 2 * z := ⟨(j + q - 2) / 2, by omega⟩
      have hzr : col z = true :=
        red_of_blue c hHe hHN (M := j - 1) (by omega)
          (fun i hi hti hiM => ih i (by omega) hi hti (by omega))
          (by omega) (fun _ => by omega) (fun _ => by omega)
      have fa := X_facts hHe hHN hb (j := q - 2) (by omega) (by omega)
      have fj := X_facts hHe hHN hb hjH hp
      have zN : z ≤ N := le_N_of_le_Hs hk hHN (show z ≤ Hs by omega)
      exact force_y c.good ⟨fa.2.1, fa.2.2⟩ ⟨fj.2.1, fj.2.2⟩ ⟨by omega, zN⟩
        (X_sum fa.1 fj.1 (by omega)) st.1 hzr

/-- **Lemma S.** Every z with t <= z <= Hs is red. -/
theorem lemmaS {k b N t Hs : Nat} {col : Nat → Bool} (c : Ctx k b N t col)
    (hHe : (k * Hs + b) % 2 = 0) (hHN : k * Hs + b ≤ 2 * N)
    {z : Nat} (htz : t ≤ z) (hzH : z ≤ Hs) : col z = true :=
  red_of_blue c hHe hHN (M := Hs) (Nat.le_refl _)
    (lemmaS_blue c hHe hHN) htz (fun _ => hzH) (fun _ => by omega)

/-! ## Lemma E (two red images) -/

/-- **Lemma E (i).** b = k m1 + s1 with 2 <= s1 <= 2t - 2, m1 <= t - 2, and
t + 1 <= H (that is k(t + 1) + b <= 2N): the colouring is not good. -/
theorem lemmaE1 {k b N t : Nat} {col : Nat → Bool} (c : Ctx k b N t col)
    {m1 s1 : Nat} (hbs : b = k * m1 + s1) (hs2 : 2 ≤ s1)
    (hs : s1 ≤ 2 * t - 2) (hm : m1 + 2 ≤ t)
    (hH : k * (t + 1) + b ≤ 2 * N) : False := by
  have hk := c.hk
  have ht := c.ht
  obtain ⟨w, hw⟩ : ∃ w, t = w + m1 := ⟨t - m1, by omega⟩
  obtain ⟨xa, xb, hx1, hx2, hx3⟩ : ∃ xa xb, xa + xb = s1 ∧ xa ≤ xb ∧ xb ≤ xa + 1 :=
    ⟨s1 / 2, s1 - s1 / 2, by omega, by omega, by omega⟩
  obtain ⟨za, zb, hz1, hz2, hz3⟩ : ∃ za zb, za + zb = w ∧ za ≤ zb ∧ zb ≤ za + 1 :=
    ⟨w / 2, w - w / 2, by omega, by omega, by omega⟩
  have e1 : k * t = k * w + k * m1 := by rw [hw, Nat.mul_add]
  have e2 : k * (t + 1) = k * t + k := by rw [Nat.mul_add, Nat.mul_one]
  have e3 : k * za + k * zb = k * w := by rw [← Nat.mul_add, hz1]
  have e4 : k * zb ≤ k * za + k := by
    have := Nat.mul_le_mul_left k hz3
    rw [Nat.mul_add, Nat.mul_one] at this
    exact this
  have e5 : k * za ≤ k * zb := Nat.mul_le_mul_left k hz2
  have e6 : 3 * t ≤ k * t := Nat.mul_le_mul_right t hk
  have hea : col (k * za + b - xa) = true :=
    force_y c.good (x := xa) (z := za) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      (c.blue xa (by omega) (by omega)) (c.blue za (by omega) (by omega))
  have heb : col (k * zb + b - xb) = true :=
    force_y c.good (x := xb) (z := zb) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      (c.blue xb (by omega) (by omega)) (c.blue zb (by omega) (by omega))
  have h := force_z c.good (x := k * za + b - xa) (y := k * zb + b - xb) (z := t)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
    hea heb
  rw [c.red] at h
  exact absurd h (by decide)

/-- **Lemma E (ii).** b = k m1 + s1 with 2 <= s1 <= 2t - 2, m1 >= t - 1,
k + b - 1 <= N and m1 + 2 <= Hs: the colouring is not good. -/
theorem lemmaE2 {k b N t Hs : Nat} {col : Nat → Bool} (c : Ctx k b N t col)
    (hHe : (k * Hs + b) % 2 = 0) (hHN : k * Hs + b ≤ 2 * N)
    {m1 s1 : Nat} (hbs : b = k * m1 + s1) (hs2 : 2 ≤ s1)
    (hs : s1 ≤ 2 * t - 2) (hm : t ≤ m1 + 1) (hN : k + b ≤ N + 1)
    (hmH : m1 + 2 ≤ Hs) : False := by
  have hk := c.hk
  have ht := c.ht
  obtain ⟨xa, xb, hx1, hx2, hx3⟩ : ∃ xa xb, xa + xb = s1 ∧ xa ≤ xb ∧ xb ≤ xa + 1 :=
    ⟨s1 / 2, s1 - s1 / 2, by omega, by omega, by omega⟩
  have e1 : k * (m1 + 2) = k * m1 + 2 * k := by rw [Nat.mul_add, Nat.mul_comm k 2]
  have b1 : col 1 = false := c.blue 1 (by omega) (by omega)
  have zN : m1 + 2 ≤ N := le_N_of_le_Hs hk hHN hmH
  have hea : col (k + b - xa) = true :=
    force_y c.good (x := xa) (z := 1) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      (c.blue xa (by omega) (by omega)) b1
  have heb : col (k + b - xb) = true :=
    force_y c.good (x := xb) (z := 1) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      (c.blue xb (by omega) (by omega)) b1
  have hz0 : col (m1 + 2) = true := lemmaS c hHe hHN (by omega) hmH
  have h := force_z c.good (x := k + b - xa) (y := k + b - xb) (z := m1 + 2)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, zN⟩ (by omega)
    hea heb
  rw [hz0] at h
  exact absurd h (by decide)

/-! ## Lemma F (the clash at k + 1) -/

/-- **Lemma F.** t <= k, 1 <= x <= t - 1, x + k <= Hs and
e = k(t - 1) + b - x <= N: the colouring is not good. (The text takes
x = min(t - 1, H* - k).) -/
theorem lemmaF {k b N t Hs : Nat} {col : Nat → Bool} (c : Ctx k b N t col)
    (hHe : (k * Hs + b) % 2 = 0) (hHN : k * Hs + b ≤ 2 * N)
    (htk : t ≤ k) {x : Nat} (hx1 : 1 ≤ x) (hxt : x < t) (hxH : x + k ≤ Hs)
    (he : k * (t - 1) + b ≤ N + x) : False := by
  have hk := c.hk
  have hb := c.hb
  have ht := c.ht
  have e1 : k * t = k * (t - 1) + k := by
    have := Nat.mul_add k (t - 1) 1
    rw [show t - 1 + 1 = t by omega, Nat.mul_one] at this
    exact this
  have e2 : k ≤ k * (t - 1) := by
    have := Nat.mul_le_mul_left k (show 1 ≤ t - 1 by omega)
    rw [Nat.mul_one] at this
    exact this
  have bx : col x = false := c.blue x hx1 hxt
  have b2 : col (t - 1) = false := c.blue (t - 1) (by omega) (by omega)
  have yN : x + k ≤ N := le_N_of_le_Hs hk hHN hxH
  have hy : col (x + k) = true := lemmaS c hHe hHN (by omega) hxH
  have hee : col (k * (t - 1) + b - x) = true :=
    force_y c.good (x := x) (z := t - 1) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) bx b2
  have h := force_z c.good (x := x + k) (y := k * (t - 1) + b - x) (z := t)
    ⟨by omega, yN⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
    hy hee
  rw [c.red] at h
  exact absurd h (by decide)

/-! ## Part B: Theorems 1 and 2 (theorem_R17-3-1.md, section 4) -/


theorem Good.mono {k b n N : Nat} {col : Nat → Bool} (h : n ≤ N)
    (g : Good k b N col) : Good k b n col :=
  fun x y z hx1 hxn hy1 hyn hz1 hzn e =>
    g x y z hx1 (by omega) hy1 (by omega) hz1 (by omega) e

theorem even_mul {k n : Nat} (h : k % 2 = 0) : (k * n) % 2 = 0 := by
  simp [Nat.mul_mod, h]

theorem even_mul_succ (k : Nat) : (k * (k + 1)) % 2 = 0 := by
  by_cases h : k % 2 = 0
  · exact even_mul h
  · rw [Nat.mul_comm]
    exact even_mul (by omega)

theorem mul_pred_add {k t : Nat} (ht : 1 ≤ t) : k * t = k * (t - 1) + k := by
  have := Nat.mul_add k (t - 1) 1
  rw [show t - 1 + 1 = t by omega, Nat.mul_one] at this
  exact this

/-- For d >= 0: z = floor(d/k) + 1 and x = k z - d, so 1 <= x <= k. -/
theorem ceil_rep {k : Nat} (d : Nat) (hk : 0 < k) :
    ∃ z x, 1 ≤ x ∧ x ≤ k ∧ x + d = k * z ∧ 1 ≤ z ∧ ∀ M, d < k * M → z ≤ M := by
  have h1 := Nat.div_add_mod d k
  have h2 := Nat.mod_lt d hk
  obtain ⟨q, hq⟩ : ∃ q, q = d / k := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = d % k := ⟨_, rfl⟩
  rw [← hq, ← hr] at h1
  rw [← hr] at h2
  have h3 : k * (q + 1) = k * q + k := by rw [Nat.mul_add, Nat.mul_one]
  refine ⟨q + 1, k - r, by omega, by omega, by omega, by omega, ?_⟩
  intro M hM
  by_cases h : q + 1 ≤ M
  · exact h
  · have h4 := Nat.mul_le_mul_left k (show M ≤ q by omega)
    omega

/-! ## Theorem 1 -/

/-- h0 = ceil((k + b)/2). -/
def h0 (k b : Nat) : Nat := (k + b + 1) / 2

/-- Theorem 1's interval: n = ceil((k h0 + b)/2). -/
def n1 (k b : Nat) : Nat := (k * h0 k b + b + 1) / 2

/-- e <= N in Lemma F with x = t - 1 (first sub-case of Theorem 1), u = t - 1. -/
theorem arith_F1 {k u b h N : Nat} (hk : 3 ≤ k) (h1 : 2 * u ≤ k)
    (h2 : k + b ≤ 2 * h) (h3 : k + 1 ≤ b) (h4 : k * h + b ≤ 2 * N) :
    k * u + b ≤ N + u := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have P1 := Nat.mul_le_mul_left (m + 2) h2
  have P2 := Nat.mul_le_mul_left (m + 1) h1
  have P3 := Nat.mul_le_mul_left m (show m + 2 ≤ b by omega)
  grind

/-- e <= N in Lemma F with x = 1, b = k + 1, h0 = k + 1 (second sub-case). -/
theorem arith_F2 {k u N : Nat} (h1 : 2 * u ≤ k)
    (h2 : k * (k + 1) + (k + 1) ≤ 2 * N) : k * u + (k + 1) ≤ N + 1 := by
  have P1 := Nat.mul_le_mul_left k h1
  grind

/-- Theorem 1 for a colouring with 1 blue. -/
theorem thm1_aux {k b : Nat} {col : Nat → Bool} (hk : 3 ≤ k) (hb : k + 1 ≤ b)
    (hpar : k % 2 = 0 → b % 2 = 0) (g : Good k b (n1 k b) col)
    (h1 : col 1 = false) : False := by
  obtain ⟨h, hh⟩ : ∃ h, h = h0 k b := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = n1 k b := ⟨_, rfl⟩
  have hh1 : k + b ≤ 2 * h ∧ 2 * h ≤ k + b + 1 := by
    rw [hh]; unfold h0; omega
  have hN1 : k * h + b ≤ 2 * N ∧ 2 * N ≤ k * h + b + 1 := by
    rw [hN, hh]; unfold n1; omega
  rw [← hN] at g
  have e3 : 3 * h ≤ k * h := Nat.mul_le_mul_right h hk
  have ehk : k * h = k * (h - 1) + k := mul_pred_add (by omega)
  obtain ⟨t, hth, c⟩ := lemma0 hk (by omega) g h1 hh1.1 hh1.2 (by omega)
  have ht := c.ht
  -- Hs: the largest j <= h0 with k j + b even
  obtain ⟨Hs, hHs1, hHs2, hHe, hHeq⟩ : ∃ Hs, h ≤ Hs + 1 ∧ Hs ≤ h ∧
      (k * Hs + b) % 2 = 0 ∧
      (Hs = h ∨ (k % 2 = 1 ∧ (k * h + b) % 2 = 1)) := by
    by_cases he : (k * h + b) % 2 = 0
    · exact ⟨h, by omega, Nat.le_refl _, he, Or.inl rfl⟩
    · have hko : k % 2 = 1 := by
        by_cases hk0 : k % 2 = 0
        · have := even_mul (n := h) hk0
          have := hpar hk0
          omega
        · omega
      exact ⟨h - 1, by omega, by omega, by omega, Or.inr ⟨hko, by omega⟩⟩
  have hHN : k * Hs + b ≤ 2 * N := by
    have := Nat.mul_le_mul_left k hHs2
    omega
  -- b = k m1 + s1 with 2 <= s1 <= k + 1
  obtain ⟨m1, s1, hbs, hs2, hsk⟩ : ∃ m1 s1, b = k * m1 + s1 ∧ 2 ≤ s1 ∧ s1 ≤ k + 1 := by
    have d1 := Nat.div_add_mod (b - 2) k
    have d2 := Nat.mod_lt (b - 2) (show 0 < k by omega)
    exact ⟨(b - 2) / k, (b - 2) % k + 2, by omega, by omega, by omega⟩
  by_cases hth0 : t = h
  · -- Case t = h0: N and N - 1 are red, and so is h0
    have blue : ∀ x, 1 ≤ x → x < h → col x = false := by
      rw [← hth0]; exact c.blue
    have red : col h = true := by rw [← hth0]; exact c.red
    have top : ∀ v, N ≤ v + 1 → v ≤ N → col v = true := by
      intro v hv1 hv2
      obtain ⟨z, x, hx1, hxk, hxd, hz1, hzM⟩ := ceil_rep (k := k) (v - b) (by omega)
      have hzh : z ≤ h - 1 := hzM (h - 1) (by omega)
      exact force_y g (x := x) (y := v) (z := z) ⟨hx1, by omega⟩
        ⟨by omega, hv2⟩ ⟨hz1, by omega⟩ (by omega)
        (blue x hx1 (by omega)) (blue z hz1 (by omega))
    have rN := top N (by omega) (Nat.le_refl _)
    have rN1 := top (N - 1) (by omega) (by omega)
    by_cases he : (k * h + b) % 2 = 0
    · have hf := force_z g (x := N) (y := N) (z := h) ⟨by omega, by omega⟩
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) rN rN
      rw [red] at hf
      exact absurd hf (by decide)
    · have hf := force_z g (x := N - 1) (y := N) (z := h) ⟨by omega, by omega⟩
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) rN1 rN
      rw [red] at hf
      exact absurd hf (by decide)
  · by_cases hs : s1 ≤ 2 * t - 2
    · -- Case t <= h0 - 1 and s1 <= 2t - 2: Lemma E
      by_cases hm : m1 + 2 ≤ t
      · have := Nat.mul_le_mul_left k (show t + 1 ≤ h by omega)
        exact lemmaE1 c hbs hs2 hs hm (by omega)
      · have e4 : 3 * m1 ≤ k * m1 := Nat.mul_le_mul_right m1 hk
        exact lemmaE2 c hHe hHN hbs hs2 hs (by omega) (by omega) (by omega)
    · -- Case t <= h0 - 1 and s1 >= 2t - 1: Lemma F
      have htk : t ≤ k := by omega
      have hHk : k + 1 ≤ Hs := by
        rcases hHeq with hH | ⟨hko, hodd⟩
        · omega
        · by_cases hc : k + 1 ≤ Hs
          · exact hc
          · exfalso
            have hhk : h = k + 1 := by omega
            have e : (k * h) % 2 = 0 := by rw [hhk]; exact even_mul_succ k
            have hb2 : b = k + 2 := by omega
            rcases Nat.lt_or_ge m1 1 with hm0 | hm0
            · have : m1 = 0 := by omega
              subst this
              omega
            · have := Nat.mul_le_mul_left k hm0
              omega
      by_cases hbig : k + t ≤ Hs + 1
      · -- x = t - 1
        exact lemmaF c hHe hHN htk (x := t - 1) (by omega) (by omega) (by omega)
          (arith_F1 hk (by omega) hh1.1 hb hN1.1)
      · -- x = 1; here b = k + 1 and h0 = k + 1 = Hs
        have hm0 : m1 = 0 := by
          rcases Nat.lt_or_ge m1 1 with hm0 | hm0
          · omega
          · have := Nat.mul_le_mul_left k hm0
            omega
        subst hm0
        have hbk : b = k + 1 := by omega
        have hhk : h = k + 1 := by omega
        subst hbk
        rw [hhk] at hN1
        exact lemmaF c hHe hHN htk (x := 1) (by omega) (by omega) (by omega)
          (arith_F2 (by omega) hN1.1)

/-- **Theorem 1.** k >= 3, b >= k + 1, b even if k is even: no 2-colouring of
[1, n], n = ceil((k ceil((k + b)/2) + b)/2), is good for x + y = k z + b. -/
theorem thm1 {k b : Nat} (hk : 3 ≤ k) (hb : k + 1 ≤ b)
    (hpar : k % 2 = 0 → b % 2 = 0) (col : Nat → Bool) :
    ¬ Good k b (n1 k b) col := by
  intro g
  cases h1 : col 1
  · exact thm1_aux hk hb hpar g h1
  · exact thm1_aux hk hb hpar (good_not g) (by simp [h1])

/-! ## Theorem 2 -/

/-- j0: the least j >= k + 1 with k j + b even. -/
def j0 (k b : Nat) : Nat := if (k * (k + 1) + b) % 2 = 0 then k + 1 else k + 2

/-- Theorem 2's interval: N2 = (k j0 + b)/2. -/
def N2 (k b : Nat) : Nat := (k * j0 k b + b) / 2

/-- j0 is k + 1 or k + 2, and k j0 + b is even. -/
theorem j0_facts {k b : Nat} (hpar : k % 2 = 0 → b % 2 = 0) :
    (j0 k b = k + 1 ∧ b % 2 = 0 ∨ j0 k b = k + 2 ∧ b % 2 = 1 ∧ k % 2 = 1) ∧
      (k * j0 k b + b) % 2 = 0 := by
  have e0 := even_mul_succ k
  have e1 : k * (k + 2) = k * (k + 1) + k := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega
  by_cases he : (k * (k + 1) + b) % 2 = 0
  · have hj : j0 k b = k + 1 := by simp only [j0, he, ↓reduceIte]
    rw [hj]
    omega
  · have hj : j0 k b = k + 2 := by simp only [j0, he, ↓reduceIte]
    rw [hj]
    have hbo : b % 2 = 1 := by omega
    have hko : k % 2 = 1 := by
      by_cases hk0 : k % 2 = 0
      · have := hpar hk0
        omega
      · omega
    omega

/-- e <= N in Lemma F with x = 1 (Theorem 2), u = t - 1. -/
theorem arith_F3 {k u b N : Nat} (h1 : 2 * u + 1 ≤ k) (hbk : b ≤ k)
    (h2 : k * (k + 1) + b ≤ 2 * N) : k * u + b ≤ N + 1 := by
  have P1 := Nat.mul_le_mul_left k h1
  grind

/-- Theorem 2 for a colouring with 1 blue. -/
theorem thm2_aux {k b : Nat} {col : Nat → Bool} (hk : 3 ≤ k) (hb1 : 1 ≤ b)
    (hbk : b ≤ k) (hpar : k % 2 = 0 → b % 2 = 0) (g : Good k b (N2 k b) col)
    (h1 : col 1 = false) : False := by
  obtain ⟨j, hj⟩ : ∃ j, j = j0 k b := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = N2 k b := ⟨_, rfl⟩
  have jf := j0_facts (k := k) (b := b) hpar
  rw [← hj] at jf
  have hN1 : 2 * N = k * j + b := by
    rw [hN, hj]; unfold N2; rw [← hj]; omega
  rw [← hN] at g
  have hj1 : k + 1 ≤ j ∧ j ≤ k + 2 := by omega
  have e1 : k * (k + 1) ≤ k * j := Nat.mul_le_mul_left k hj1.1
  have e2 : 3 * (k + 1) ≤ k * (k + 1) := Nat.mul_le_mul_right (k + 1) hk
  obtain ⟨t, hth, c⟩ := lemma0 (h := (k + b + 1) / 2) hk hb1 g h1
    (by omega) (by omega) (by omega)
  have ht := c.ht
  by_cases hE : 2 ≤ b ∧ b ≤ 2 * t - 2
  · -- Lemma E (i) with m1 = 0, s1 = b
    have := Nat.mul_le_mul_left k (show t + 1 ≤ j by omega)
    exact lemmaE1 c (m1 := 0) (s1 := b) (by omega) hE.1 hE.2 (by omega) (by omega)
  · -- Lemma F with x = 1
    have hko : b = 1 → k % 2 = 1 := by
      intro hb
      by_cases hk0 : k % 2 = 0
      · have := hpar hk0
        omega
      · omega
    have hu : 2 * (t - 1) + 1 ≤ k := by
      by_cases hb : b = 1
      · have := hko hb
        omega
      · omega
    exact lemmaF c jf.2 (by omega) (by omega) (x := 1) (by omega) (by omega)
      (by omega) (arith_F3 hu hbk (by omega))

/-- **Theorem 2.** k >= 3, 1 <= b <= k, b even if k is even: no 2-colouring of
[1, N2], N2 = (k j0 + b)/2, is good for x + y = k z + b. -/
theorem thm2 {k b : Nat} (hk : 3 ≤ k) (hb1 : 1 ≤ b) (hbk : b ≤ k)
    (hpar : k % 2 = 0 → b % 2 = 0) (col : Nat → Bool) :
    ¬ Good k b (N2 k b) col := by
  intro g
  cases h1 : col 1
  · exact thm2_aux hk hb1 hbk hpar g h1
  · exact thm2_aux hk hb1 hbk hpar (good_not g) (by simp [h1])

/-! ## Part C: Lemma A, the reflection, the Martinelli-Schaal lower bound, and
the theorem (theorem_R17-3-1.md, section 5) -/

/-! ## The statement's definitions -/

/-- `col` has a monochromatic solution of x + y + c = k z in [1, n]^3. -/
def HasMono (c k n : Nat) (col : Nat → Bool) : Prop :=
  ∃ x y z : Nat, (1 ≤ x ∧ x ≤ n) ∧ (1 ≤ y ∧ y ≤ n) ∧ (1 ≤ z ∧ z ≤ n) ∧
    x + y + c = k * z ∧ col x = col y ∧ col y = col z

/-- Every 2-colouring of [1, n] has a monochromatic solution of
x + y + c = k z. -/
def Forced (c k n : Nat) : Prop := ∀ col : Nat → Bool, HasMono c k n col

/-- R is the 2-colour Rado number R(c, k): the least n such that every
2-colouring of [1, n] has a monochromatic solution of x + y + c = k z. -/
def IsRado (c k R : Nat) : Prop := Forced c k R ∧ ∀ n, n < R → ¬ Forced c k n

/-- c is valid for k: k is odd or c is even. -/
def Valid (c k : Nat) : Prop := k % 2 = 1 ∨ c % 2 = 0

/-! ## Arithmetic -/

/-- q = ceil(a/k) = (a + k - 1)/k satisfies a <= k q <= a + k - 1. -/
theorem ceil_spec {a k : Nat} (hk : 0 < k) :
    a ≤ k * ((a + k - 1) / k) ∧ k * ((a + k - 1) / k) ≤ a + k - 1 := by
  have h1 := Nat.div_add_mod (a + k - 1) k
  have h2 := Nat.mod_lt (a + k - 1) hk
  obtain ⟨q, hq⟩ : ∃ q, q = (a + k - 1) / k := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = (a + k - 1) % k := ⟨_, rfl⟩
  rw [← hq, ← hr] at h1
  rw [← hr] at h2
  rw [← hq]
  omega

/-- 2 c*(k) = k^3 + k^2 - 4k for odd k, k^3 - 2k for even k. -/
theorem two_cstar {k : Nat} (hk : 3 ≤ k) :
    (k % 2 = 1 → 2 * cstar k + 4 * k = k * k * k + k * k) ∧
      (k % 2 = 0 → 2 * cstar k + 2 * k = k * k * k) := by
  constructor
  · intro ho
    obtain ⟨i, hi⟩ : ∃ i, k = 2 * (i + 1) + 1 := ⟨(k - 3) / 2, by omega⟩
    rw [T2.cstar_odd hi (by omega)]
    have e : k * (i + 1) + 2 * (i + 1) - 1 = k * (i + 1) + 2 * i + 1 := by omega
    rw [e]
    subst hi
    grind
  · intro he
    obtain ⟨i, hi⟩ : ∃ i, k = 2 * (i + 2) := ⟨(k - 4) / 2, by omega⟩
    rw [T2.cstar_even hi (by omega)]
    have h1 : 1 ≤ k * (i + 2) := Nat.mul_pos (by omega) (by omega)
    have e := mul_pred_add (k := k) h1
    obtain ⟨p, hp⟩ : ∃ p, p = k * (k * (i + 2) - 1) := ⟨_, rfl⟩
    rw [← hp] at e ⊢
    subst hi
    grind

/-- Lemma A, b >= 1. -/
theorem arith_A1 {m A N c cs : Nat}
    (h1 : (m + 2) * A ≤ c + 2 + (m + 2) - 1)
    (h2 : (m + 2) * N ≤ 2 * A + c + (m + 2) - 1)
    (hcs : (m + 2) * (m + 2) * (m + 2) ≤ 2 * cs + 2 * (m + 2))
    (hc : cs < c) : m * (N + 1) + 1 ≤ c := by
  by_cases hn : m * (N + 1) + 1 ≤ c
  · exact hn
  · exfalso
    have hc' : c ≤ m * N + m := by grind
    have hNA : N ≤ A + m := by grind
    have P1 := Nat.mul_le_mul_left m hNA
    have hA : 2 * A ≤ m * m + 2 * m + 3 := by grind
    have P2 := Nat.mul_le_mul_left m hA
    grind

/-- Lemma A, b >= k + 1: k h0 + b <= 2N. -/
theorem arith_A2 {m A N b h : Nat}
    (h1 : m * (N + 1) + b + 2 ≤ (m + 2) * A)
    (h2 : 2 * A + (m * (N + 1) + b) ≤ (m + 2) * N)
    (hh : 2 * h ≤ m + 2 + b + 1) : (m + 2) * h + b ≤ 2 * N := by
  have hAN : 2 * A + m + b ≤ 2 * N := by grind
  obtain ⟨H, hH⟩ : ∃ H, N + 1 = H + A := ⟨N + 1 - A, by omega⟩
  have P1 := Nat.mul_le_mul_left (m + 2) (show h ≤ H by omega)
  have e1 : (m + 2) * (N + 1) = (m + 2) * H + (m + 2) * A := by
    rw [hH, Nat.mul_add]
  grind

/-- Lemma A, b <= k: N <= N2 - 1 gives c <= c*(k). -/
theorem arith_A3 {m N b j c cs : Nat}
    (hc : c = m * (N + 1) + b) (hN : 2 * (N + 1) ≤ (m + 2) * j + b)
    (hj : j = m + 3 ∧ b % 2 = 0 ∨ j = m + 4 ∧ m % 2 = 1) (hbk : b ≤ m + 2)
    (ho : m % 2 = 1 →
      2 * cs + 4 * (m + 2) = (m + 2) * (m + 2) * (m + 2) + (m + 2) * (m + 2))
    (he : m % 2 = 0 → 2 * cs + 2 * (m + 2) = (m + 2) * (m + 2) * (m + 2)) :
    c ≤ cs := by
  have P1 := Nat.mul_le_mul_left m hN
  rcases hj with ⟨rfl, hb⟩ | ⟨rfl, hm⟩
  · by_cases hm : m % 2 = 0
    · have t := he hm
      have P2 := Nat.mul_le_mul_left (m + 2) hbk
      grind
    · have t := ho (by omega)
      have P2 := Nat.mul_le_mul_left (m + 2) (show b ≤ m + 1 by omega)
      grind
  · have t := ho hm
    have P2 := Nat.mul_le_mul_left (m + 2) hbk
    grind

/-! ## Lemma A -/

/-- **Lemma A.** k >= 3, c > c*(k) valid, N = LB(c, k): then
c = (k - 2)(N + 1) + b with b >= 1 (b even if k is even);
N >= ceil((k h0 + b)/2) if b >= k + 1; and N >= N2 if b <= k. -/
theorem lemmaA {k c : Nat} (hk : 3 ≤ k) (hc : cstar k < c) (hval : Valid c k) :
    ∃ b, 1 ≤ b ∧ c = (k - 2) * (LB c k + 1) + b ∧ (k % 2 = 0 → b % 2 = 0) ∧
      (k + 1 ≤ b → n1 k b ≤ LB c k) ∧ (b ≤ k → N2 k b ≤ LB c k) := by
  have hkpos : 0 < k := by omega
  obtain ⟨A, hA⟩ : ∃ A, A = (c + 2 + k - 1) / k := ⟨_, rfl⟩
  have sA := ceil_spec (a := c + 2) hkpos
  rw [← hA] at sA
  have sN := ceil_spec (a := 2 * A + c) hkpos
  have hL : LB c k = (2 * A + c + k - 1) / k := by rw [hA]; rfl
  rw [← hL] at sN
  obtain ⟨N, hN⟩ : ∃ N, N = LB c k := ⟨_, rfl⟩
  rw [← hN] at sN ⊢
  have tc := two_cstar hk
  obtain ⟨cs, hcs⟩ : ∃ cs, cs = cstar k := ⟨_, rfl⟩
  rw [← hcs] at tc hc
  obtain ⟨m, hm⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  subst hm
  rw [show m + 2 - 2 = m by omega]
  have hkk : 3 * (m + 2) ≤ (m + 2) * (m + 2) := Nat.mul_le_mul_right _ hk
  have hcs3 : (m + 2) * (m + 2) * (m + 2) ≤ 2 * cs + 2 * (m + 2) := by
    by_cases hp : (m + 2) % 2 = 1
    · have := tc.1 hp
      omega
    · have := tc.2 (by omega)
      omega
  have hb : m * (N + 1) + 1 ≤ c := arith_A1 sA.2 sN.2 hcs3 hc
  obtain ⟨b, hbc⟩ : ∃ b, c = m * (N + 1) + b := ⟨c - m * (N + 1), by omega⟩
  refine ⟨b, by omega, hbc, ?_, ?_, ?_⟩
  · intro h
    have h1 : c % 2 = 0 := by
      rcases hval with h2 | h2
      · omega
      · exact h2
    have h3 := even_mul (k := m) (n := N + 1) (by omega)
    omega
  · intro hbk
    obtain ⟨h, hh⟩ : ∃ h, h = h0 (m + 2) b := ⟨_, rfl⟩
    have hh1 : 2 * h ≤ m + 2 + b + 1 := by rw [hh]; unfold h0; omega
    have h4 : (m + 2) * h + b ≤ 2 * N :=
      arith_A2 (A := A) (by omega) (by omega) hh1
    unfold n1
    rw [← hh]
    omega
  · intro hbk
    have jf := j0_facts (k := m + 2) (b := b) (fun h => by
      rcases hval with h2 | h2
      · omega
      · have h3 := even_mul (k := m) (n := N + 1) (by omega)
        omega)
    by_cases hlt : N2 (m + 2) b ≤ N
    · exact hlt
    · exfalso
      obtain ⟨j, hj⟩ : ∃ j, j = j0 (m + 2) b := ⟨_, rfl⟩
      rw [← hj] at jf
      have h5 : 2 * N2 (m + 2) b = (m + 2) * j + b := by
        unfold N2; rw [← hj]; omega
      have h6 : c ≤ cs :=
        arith_A3 (j := j) hbc (by omega) (by omega) hbk
          (fun h => tc.1 (by omega)) (fun h => tc.2 (by omega))
      omega

/-! ## Upper bound: reflection, then Theorems 1 and 2 -/

/-- R(c, k) <= LB(c, k) for valid c > c*(k): every 2-colouring of
[1, LB(c, k)] has a monochromatic solution of x + y + c = k z. -/
theorem upper {k c : Nat} (hk : 3 ≤ k) (hc : cstar k < c) (hval : Valid c k) :
    Forced c k (LB c k) := by
  obtain ⟨b, hb1, hcb, hpar, hA1, hA2⟩ := lemmaA hk hc hval
  obtain ⟨N, hN⟩ : ∃ N, N = LB c k := ⟨_, rfl⟩
  rw [← hN] at hcb hA1 hA2 ⊢
  intro col
  -- the reflected colouring x -> col (N + 1 - x) is not good for x + y = k z + b
  have hng : ¬ Good k b N (fun x => col (N + 1 - x)) := by
    intro g
    by_cases hbk : b ≤ k
    · exact thm2 hk hb1 hbk hpar _ (g.mono (hA2 hbk))
    · exact thm1 hk (by omega) hpar _ (g.mono (hA1 (by omega)))
  obtain ⟨x, y, z, hx, hy, hz, e, c1, c2⟩ := exists_mono hng
  refine ⟨N + 1 - x, N + 1 - y, N + 1 - z, by omega, by omega, by omega, ?_,
    c1, c2⟩
  obtain ⟨m, hm⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  subst hm
  rw [show m + 2 - 2 = m by omega] at hcb
  obtain ⟨z', hz'⟩ : ∃ z', N + 1 = z + z' := ⟨N + 1 - z, by omega⟩
  rw [show N + 1 - z = z' by omega]
  have e1 : (m + 2) * (N + 1) = (m + 2) * z + (m + 2) * z' := by
    rw [hz', Nat.mul_add]
  have e2 : (m + 2) * (N + 1) = m * (N + 1) + 2 * (N + 1) := Nat.add_mul ..
  omega

/-! ## Lower bound (Martinelli and Schaal): [1, a - 1] red, [a, LB - 1] blue -/

/-- The two-block colouring: x is red iff x < a, a = ceil((c + 2)/k). -/
def blockCol (c k x : Nat) : Bool := decide (x < (c + 2 + k - 1) / k)

/-- The two-block colouring has no monochromatic solution of x + y + c = k z
with x, y >= 1 and z <= LB(c, k) - 1. -/
theorem lower_col {c k : Nat} (hk : 0 < k) (x y z : Nat) (hx : 1 ≤ x)
    (hy : 1 ≤ y) (hz : z < LB c k) (e : x + y + c = k * z) :
    ¬ (blockCol c k x = blockCol c k y ∧ blockCol c k y = blockCol c k z) := by
  intro ⟨c1, c2⟩
  obtain ⟨A, hA⟩ : ∃ A, A = (c + 2 + k - 1) / k := ⟨_, rfl⟩
  have sA := ceil_spec (a := c + 2) hk
  rw [← hA] at sA
  have sN := ceil_spec (a := 2 * A + c) hk
  have hL : LB c k = (2 * A + c + k - 1) / k := by rw [hA]; rfl
  rw [← hL] at sN
  unfold blockCol at c1 c2
  rw [← hA] at c1 c2
  have i1 : x < A ↔ y < A := decide_eq_decide.mp c1
  have i2 : y < A ↔ z < A := decide_eq_decide.mp c2
  have P1 := Nat.mul_le_mul_left k (show z + 1 ≤ LB c k by omega)
  rw [Nat.mul_add, Nat.mul_one] at P1
  by_cases hzA : z < A
  · have P2 := Nat.mul_le_mul_left k (show z + 1 ≤ A by omega)
    rw [Nat.mul_add, Nat.mul_one] at P2
    omega
  · omega

/-- R(c, k) >= LB(c, k): no n < LB(c, k) is forced. -/
theorem lower {c k n : Nat} (hk : 0 < k) (hn : n < LB c k) : ¬ Forced c k n := by
  intro hf
  obtain ⟨x, y, z, hx, _, hz, e, c1, c2⟩ := hf (blockCol c k)
  exact lower_col hk x y z hx.1 (by omega) (by omega) e ⟨c1, c2⟩

/-! ## The theorem -/

theorem Forced.mono {c k n n' : Nat} (h : n ≤ n') (f : Forced c k n) :
    Forced c k n' := fun col =>
  let ⟨x, y, z, hx, hy, hz, e, c1, c2⟩ := f col
  ⟨x, y, z, ⟨hx.1, by omega⟩, ⟨hy.1, by omega⟩, ⟨hz.1, by omega⟩, e, c1, c2⟩

/-- R(c, k) = LB(c, k) for every valid c > c*(k). -/
theorem rado_eq_LB {k c : Nat} (hk : 3 ≤ k) (hc : cstar k < c)
    (hval : Valid c k) : IsRado c k (LB c k) :=
  ⟨upper hk hc hval, fun _ hn => lower (by omega) hn⟩

/-- R(c*(k), k) > LB(c*(k), k): some 2-colouring of [1, LB(c*(k), k)] has no
monochromatic solution (T2, round 17). -/
theorem not_forced_cstar {k : Nat} (hk : 3 ≤ k) :
    ¬ Forced (cstar k) k (LB (cstar k) k) := by
  intro hf
  obtain ⟨col, h⟩ := T2.T2 k hk
  obtain ⟨x, y, z, hx, hy, hz, e, c1, c2⟩ := hf col
  exact h x y z hx.1 hx.2 hy.1 hy.2 hz.1 hz.2 e ⟨c1, c2⟩

/-- c*(k) is valid: it is even when k is even. -/
theorem valid_cstar {k : Nat} (hk : 3 ≤ k) : Valid (cstar k) k := by
  by_cases ho : k % 2 = 1
  · exact Or.inl ho
  · refine Or.inr ?_
    rw [T2.cstar_even (j := k / 2) (by omega) (by omega)]
    exact even_mul (by omega)

/-- **R17-3-1**, with every notion written out. For every k >= 3:
(1) for every valid c > c*(k) (k odd or c even), every 2-colouring of
[1, LB(c, k)] has a monochromatic solution of x + y + c = k z, and some
2-colouring of [1, LB(c, k) - 1] has none, so R(c, k) = LB(c, k);
(2) some 2-colouring of [1, LB(c*(k), k)] has no monochromatic solution of
x + y + c*(k) = k z, so R(c*(k), k) > LB(c*(k), k). -/
theorem R17_3_1 (k : Nat) (hk : 3 ≤ k) :
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
  ⟨fun c hc hval =>
    ⟨upper hk hc hval, blockCol c k, fun x y z hx _ hy _ _ hz e =>
      lower_col (by omega) x y z hx hy hz e⟩,
    T2.T2 k hk⟩

/-- **R17-3-1** in terms of the Rado number: for every k >= 3,
R(c, k) = LB(c, k) for every valid c > c*(k), and R(c*(k), k) > LB(c*(k), k):
[1, LB(c*(k), k)] is not forced, so any Rado number of c*(k) exceeds
LB(c*(k), k). -/
theorem R17_3_1_rado (k : Nat) (hk : 3 ≤ k) :
    (∀ c, cstar k < c → Valid c k → IsRado c k (LB c k)) ∧
      ¬ Forced (cstar k) k (LB (cstar k) k) ∧
      ∀ R, IsRado (cstar k) k R → LB (cstar k) k < R := by
  refine ⟨fun c hc hval => rado_eq_LB hk hc hval, not_forced_cstar hk, ?_⟩
  intro R hR
  rcases Nat.lt_or_ge (LB (cstar k) k) R with h | h
  · exact h
  · exact absurd (hR.1.mono h) (not_forced_cstar hk)

/-- nu(k): "R(c, k) = LB(c, k) for every valid c >= v" holds exactly when
v > c*(k). So the least such v is c*(k) + 1, and the least valid one is
c*(k) + 1 for odd k and c*(k) + 2 for even k (c*(k) is valid). -/
theorem nu_iff (k : Nat) (hk : 3 ≤ k) (v : Nat) :
    (∀ c, v ≤ c → Valid c k → IsRado c k (LB c k)) ↔ cstar k < v := by
  constructor
  · intro h
    rcases Nat.lt_or_ge (cstar k) v with h1 | h1
    · exact h1
    · exact absurd (h (cstar k) h1 (valid_cstar hk)).1 (not_forced_cstar hk)
  · intro h c hc hval
    exact rado_eq_LB hk (by omega) hval

/-! ## Small values against the text (kernel `decide`) -/

/-- `nu(k) = c*(k) + 1` (`k` odd), `c*(k) + 2` (`k` even) for `k = 3..10`:
`13, 30, 66, 104, 183, 250, 388, 492`. -/
theorem nu_small_values :
    cstar 3 + 1 = 13 ∧ cstar 4 + 2 = 30 ∧ cstar 5 + 1 = 66 ∧
    cstar 6 + 2 = 104 ∧ cstar 7 + 1 = 183 ∧ cstar 8 + 2 = 250 ∧
    cstar 9 + 1 = 388 ∧ cstar 10 + 2 = 492 := by decide

/-- At `k = 5, c = 66`: `R(66, 5) = LB(66, 5) = 19`. -/
theorem rado_66_5 : IsRado 66 5 19 :=
  rado_eq_LB (k := 5) (c := 66) (by decide) (by decide) (Or.inl (by decide))

/-- The printed Kim–Song–Hwang (2023) conjecture `ν(5) = 66`:
`R(c, 5) = LB(c, 5)` for every valid `c >= 66`, and not for every valid `c >= 65`. -/
theorem nu_5_eq_66 :
    (∀ c, 66 ≤ c → Valid c 5 → IsRado c 5 (LB c 5)) ∧
    ¬ (∀ c, 65 ≤ c → Valid c 5 → IsRado c 5 (LB c 5)) :=
  ⟨(nu_iff 5 (by decide) 66).mpr (by decide),
    fun h => absurd ((nu_iff 5 (by decide) 65).mp h) (by decide)⟩

/-- Theorems 1 and 2 at `k = 5`: the intervals for `b = 6` and `b = 5, 1`. -/
theorem intervals_k5 : n1 5 6 = 18 ∧ N2 5 5 = 20 ∧ N2 5 1 = 18 := by decide

end RadoNu
