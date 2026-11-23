module

public import RadoNu

/-!
# Axiom Verification Audit for `RadoNu`

Prints the Lean 4 kernel axioms used by every formalized theorem, lemma,
proposition, and corollary in `RadoNu` (covering Top-20 Rank #17
discovery `R17-3-1`: exact two-colour Rado last exception `ν(k)` for all
`k ≥ 3`). A clean audit must show ONLY Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) — NEVER `sorryAx`, `Lean.ofReduceBool`,
`Lean.trustCompiler`, or any custom axiom.
-/

-- Lower half T2: R(c*(k), k) > LB(c*(k), k) for all k >= 3
#print axioms RadoNu.T2.div_eq_of_decomp
#print axioms RadoNu.T2.mod_eq_of_decomp
#print axioms RadoNu.T2.sum_lt_two
#print axioms RadoNu.T2.shift
#print axioms RadoNu.T2.sq_odd
#print axioms RadoNu.T2.cstar_odd
#print axioms RadoNu.T2.LB_odd
#print axioms RadoNu.T2.colOdd_eq
#print axioms RadoNu.T2.odd_case
#print axioms RadoNu.T2.sq_even
#print axioms RadoNu.T2.mul_pred
#print axioms RadoNu.T2.q_even
#print axioms RadoNu.T2.cstar_even
#print axioms RadoNu.T2.LB_even
#print axioms RadoNu.T2.even_case
#print axioms RadoNu.T2.LB_cstar
#print axioms RadoNu.T2.T2_col
#print axioms RadoNu.T2.T2

-- Part A: reflected equation x + y = k z + b, forcing rules, Lemmas 0, S, E, F
#print axioms RadoNu.force_z
#print axioms RadoNu.force_y
#print axioms RadoNu.force_xx
#print axioms RadoNu.good_not
#print axioms RadoNu.exists_mono
#print axioms RadoNu.least_true
#print axioms RadoNu.lemma0
#print axioms RadoNu.X_facts
#print axioms RadoNu.X_sum
#print axioms RadoNu.le_N_of_le_Hs
#print axioms RadoNu.lemmaS_start
#print axioms RadoNu.red_of_blue
#print axioms RadoNu.lemmaS_blue
#print axioms RadoNu.lemmaS
#print axioms RadoNu.lemmaE1
#print axioms RadoNu.lemmaE2
#print axioms RadoNu.lemmaF

-- Part B: Theorems 1 and 2
#print axioms RadoNu.Good.mono
#print axioms RadoNu.even_mul
#print axioms RadoNu.even_mul_succ
#print axioms RadoNu.mul_pred_add
#print axioms RadoNu.ceil_rep
#print axioms RadoNu.arith_F1
#print axioms RadoNu.arith_F2
#print axioms RadoNu.thm1_aux
#print axioms RadoNu.thm1
#print axioms RadoNu.j0_facts
#print axioms RadoNu.arith_F3
#print axioms RadoNu.thm2_aux
#print axioms RadoNu.thm2

-- Part C: Lemma A, reflection, Martinelli-Schaal lower bound, and main theorems
#print axioms RadoNu.ceil_spec
#print axioms RadoNu.two_cstar
#print axioms RadoNu.arith_A1
#print axioms RadoNu.arith_A2
#print axioms RadoNu.arith_A3
#print axioms RadoNu.lemmaA
#print axioms RadoNu.upper
#print axioms RadoNu.lower_col
#print axioms RadoNu.lower
#print axioms RadoNu.Forced.mono
#print axioms RadoNu.rado_eq_LB
#print axioms RadoNu.not_forced_cstar
#print axioms RadoNu.valid_cstar
#print axioms RadoNu.R17_3_1
#print axioms RadoNu.R17_3_1_rado
#print axioms RadoNu.nu_iff

-- Small-k values and Kim-Song-Hwang (2023) conjecture nu(5) = 66
#print axioms RadoNu.nu_small_values
#print axioms RadoNu.rado_66_5
#print axioms RadoNu.nu_5_eq_66
#print axioms RadoNu.intervals_k5
