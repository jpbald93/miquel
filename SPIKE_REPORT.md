# Miquel's theorem — Lean 4 / Mathlib spike (jack:~/miquel)

**Status: DONE.** Gate PASS (clean `rm -rf .lake/build; lake build`: 0 errors, 0 warnings; forbidden-token grep empty; `#print axioms` shows only `propext, Classical.choice, Quot.sound`). Not pushed.

## Prior art
An earlier attempt checked Mathlib (source, docs/100.yaml, docs/1000.yaml: no `miquel` declaration), `gh search` code/repos/PRs, Isabelle AFP, HOL Light, Coq/Rocq and Mizar, and found no complete formal proof of Miquel's theorem. I did not redo that search. (GeoCoq-style synthetic libraries and Wu/Gröbner provers treat Miquel as a standard benchmark. They are automated-prover benchmarks, not library theorems.)

## Model
The plane is `ℂ` and distance is Mathlib's `dist`. `Dp a b c` = −(cross product of `b−a`, `c−a`), so `Dp A B C ≠ 0` ⇔ A, B, C are not collinear. Points on the sides are given by real parameters, and the **extended** sides are allowed:
`F = A + n(B−A)` (line AB), `E = A + t(C−A)` (line CA), `D = B + u(C−B)` (line BC). The hypotheses `n,t,u ∉ {0,1}` say that D, E, F are not vertices. They are exactly what is needed for the triples (A,E,F), (B,F,D), (C,D,E) to be non-collinear, so each of the three circles exists and is unique.

## Headline statements (copied from source)
`Miquel/Main.lean:54`
```lean
theorem miquel {A B C D E F : ℂ} {n t u : ℝ} (hABC : Dp A B C ≠ 0)
    (hF : F = A + (n : ℂ) * (B - A)) (hE : E = A + (t : ℂ) * (C - A))
    (hD : D = B + (u : ℂ) * (C - B))
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    ∃ M : ℂ,
      (∀ (O : ℂ) (r : ℝ), dist A O = r → dist E O = r → dist F O = r → dist M O = r) ∧
      (∀ (O : ℂ) (r : ℝ), dist B O = r → dist F O = r → dist D O = r → dist M O = r) ∧
      (∀ (O : ℂ) (r : ℝ), dist C O = r → dist D O = r → dist E O = r → dist M O = r)
```
`Miquel/Main.lean:97` (concyclic form: the three circles exist and share M)
```lean
theorem miquel_concyclic ... (same hypotheses) :
    ∃ O₁ O₂ O₃ M : ℂ,
      dist E O₁ = dist A O₁ ∧ dist F O₁ = dist A O₁ ∧ dist M O₁ = dist A O₁ ∧
      dist F O₂ = dist B O₂ ∧ dist D O₂ = dist B O₂ ∧ dist M O₂ = dist B O₂ ∧
      dist D O₃ = dist C O₃ ∧ dist E O₃ = dist C O₃ ∧ dist M O₃ = dist C O₃
```
- `miquel_example` (Main.lean:136): non-vacuity. Uses A=0, B=4, C=1+3i with D, E, F the side midpoints. All hypotheses are discharged and the theorem gives circles and a Miquel point.
- `miquel_negative_control` (Main.lean:155): in the same configuration, F (which lies on circles 1 and 2) lies on **no** circle through C, D, E. So membership of the third circle is a real constraint. Numerically |F−O₃|−r₃ ≈ 0.94.

## Proof architecture
- `Basic.lean` (from the earlier attempt): concyclicity determinant `Q` and `Q_eq_zero_of_dist`.
- `Coeffs.lean`: translation-invariant frame with `B=A+w`, `C=A+c`, `M=F+(x,y)`. The three circle polynomials `q1, q2, q3` are given explicitly. The algebraic **certificate** has `K = n t u (n−1)|w|²`:
  `cert_x : K·x·q3 = P₁ q1 + P₂ q2`, `cert_y : K·y·q3 = P₁' q1 + P₂' q2`. P, P' are linear in (x,y), and SymPy computed them by solving the linear system. Two more identities support the argument: `tang : K·k3 = (t−1)(u−1)·(linear-part cross product)`, which handles M = F, and `sep`, which shows the radical-axis normal is non-zero. Every identity is checked by `ring`.
  (A plain `Q3 = P·Q1 + Q·Q2` with linear P, Q is *impossible*: q1 and q2 have no constant term but q3 does. Multiplying by x or y fixes this, and the tangency identity covers the remaining case M = F.)
- `Frame.lean`: radical-axis point `rpx, rpy` lies on both circles (`rp_on`). The abstract `core` lemma uses the certificates to show it lies on the third circle, giving `frame`. Also proves the circumcentre lemma `exists_circle` and `dist_eq_of_Q_eq_zero` (Q=0 plus three non-collinear points on a circle ⇒ the fourth point is on it).
- `Main.lean`: coordinate `bridge` (Q, Dp ↦ frame polynomials, by `ring`), then `miquel`, `miquel_concyclic`, the example and the negative control.

## Numerics
`code/check_miquel.py` (earlier attempt) and `code/check_miquel_formal.py` (this run). The second checks the exact formal configuration with extended sides over 20k random cases: worst relative residual 2.3e-11. The negative control F on circle 3 has residual ≥ 2.7e-5.

## Gate output
```
lake build (clean): ✔ Built Miquel.Basic / Miquel.Coeffs (22s) / Miquel.Frame / Miquel.Main / Miquel
Build completed successfully (8711 jobs). EXIT 0   — grep -ciE "warning|error" build.log → 0
forbidden grep: (empty) grep exit 1
'Miquel.miquel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Miquel.miquel_concyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Miquel.miquel_example' depends on axioms: [propext, Classical.choice, Quot.sound]
'Miquel.miquel_negative_control' depends on axioms: [propext, Classical.choice, Quot.sound]
'Miquel.frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'Miquel.cert_x' depends on axioms: [propext, Classical.choice, Quot.sound]
'Miquel.cert_y' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Not done / caveats
- The statement is in `ℂ` with explicit coordinates and `dist`. It is not phrased with Mathlib's `EuclideanGeometry.Sphere` / `Cospherical` API, though restating it that way would be routine.
- Degenerate cases are excluded rather than handled: a collinear triangle, or D/E/F at a vertex (where a "circle" through two coincident points is not unique).
- M is not proved distinct from D, E, F. It can coincide with them in tangent configurations; the theorem allows this.
- The Miquel-point corollaries (spiral similarity, Miquel quadrilateral/pentagon) are not formalised.
