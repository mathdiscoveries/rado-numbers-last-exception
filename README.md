# The Last Exception for Two-Colour Rado Numbers (`x + y + c = kz`)

Pure core Lean 4 (`v4.35.0`, **zero external dependencies / zero Mathlib imports**, `0 sorry`, `0 native_decide`, standard axioms only) formalization proving both halves of the exact last-exception formula for the 2-colour Rado number $R(c, k)$ of $x + y + c = kz$ for every integer $k \ge 3$:

$$c^*(k) = \begin{cases} \dfrac{k(k^2 + k - 4)}{2} & (k \text{ odd}), \\[6pt] \dfrac{k(k^2 - 2)}{2} & (k \text{ even}), \end{cases}$$

so that $R(c, k) = \mathrm{LB}(c, k)$ for every valid $c > c^*(k)$ (where valid means $k$ odd or $c$ even), while $[1, \mathrm{LB}(c^*(k), k)]$ admits a 2-colouring with no monochromatic solution (`¬ Forced (cstar k) k (LB (cstar k) k)`, so $c^*(k)$ is an exception to $R(c, k) = \mathrm{LB}(c, k)$; finite existence of $R(c^*(k), k)$ itself is not formalized). In `nu_iff`, the property "$R(c, k) = \mathrm{LB}(c, k)$ for all valid $c \ge v$" holds for all natural-number cutoffs $v > c^*(k)$ (so the least integer cutoff is $c^*(k) + 1$), while restricting to valid cutoffs (`Valid (ν(k)) k`, i.e., even when $k$ is even) gives the least valid cutoff $\nu(k) = c^*(k) + 1$ for odd $k$ and $c^*(k) + 2$ for even $k$, namely $13, 30, 66, 104, 183, 250, 388, 492, \dots$ for $k = 3, \dots, 10$, settling the conjecture $\nu(5) = 66$ of Kim, Song, and Hwang (2023).

## Provenance & Review Status

- **Author:** Tyler B. Hughes (`mathdiscoveries.org/results/rado-numbers-last-exception`)
- **Discovery & formalization:** Generated and checked by AI research agents built and directed by Tyler B. Hughes.
- **Referee status:** No human mathematician has yet refereed the proof.
- **Attribution:** The lower bound $\mathrm{LB}(c, k)$ and lower-half exception theorem (Lemma 3) are due to Martinelli and Schaal (2007); the upper-half proof for all $k \ge 3$ and the complete Lean 4 formalization of both halves are presented here.

## Build & Verify

```sh
lake build
lake env lean RadoNu/Verify.lean
```

## Layout

- `Challenge.lean`: Self-contained definitions and theorem statements (`RadoNuChallenge.*`) for Palomar comparison.
- `Solution.lean`: Proofs connecting `RadoNuChallenge.*` to `RadoNu.*`.
- `RadoNu/RadoNu.lean`: Complete core Lean 4 proof (both lower and upper halves, 68 declarations).
- `RadoNu/Verify.lean`: `#print axioms` audit for every theorem and helper lemma.
- `comparator.json` & `formalization.yaml`: Palomar Registry v0.4 metadata.
