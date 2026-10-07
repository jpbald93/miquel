import Miquel.Main

/-!
# Definition bridges

Each locally defined notion of the development is tied here to the standard notion it is meant
to express, so that a reader need not trust the docstrings.

* `Dp` is (minus) the `3 × 3` orientation determinant, and vanishes exactly on collinear triples
  in the sense of Mathlib's `Collinear`.
* `Q` is the `4 × 4` concyclicity determinant `det [x, y, x² + y², 1]`, and equals
  `Dp P R S` times Mathlib's power of a point (`EuclideanGeometry.Sphere.power`) with respect to
  the circle through `P, R, S`.
* The frame coefficients of `Miquel.Coeffs`: `alᵢ` is the orientation of the `i`-th triangle
  (zero iff collinear); `lxᵢ, lyᵢ` are `2 alᵢ` times the coordinates of `F` minus the
  circumcentre; `kk3` is `al3` times the power of `F` with respect to the circle `(CDE)`;
  `qᵢ` is `alᵢ` times the power of the test point `M`; `KK = n t u (n - 1) |AB|²`.
* `certx1, certx2, certy1, certy2` have no standard counterpart: they are certificate
  multipliers, and their bridge records exactly the role they play.
* `circX, circY`: any point equidistant from `P, R, S` has these coordinates (times `2 Dp`), so
  they describe the (unique) circumcentre.
* `rpN` vanishes iff the two circle polynomials are proportional (the radical axis is undefined);
  `rpx, rpy` is the only common zero of the two circles other than the origin.
-/

noncomputable section

namespace Miquel

open Complex EuclideanGeometry

/-! ### Orientation and the concyclicity determinant -/

/-- `Dp a b c` is minus the orientation determinant `det [x, y, 1]` of `a, b, c`. -/
theorem Dp_eq_neg_det (a b c : ℂ) : Dp a b c =
    -Matrix.det !![a.re, a.im, 1; b.re, b.im, 1; c.re, c.im, 1] := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.head_fin_const, Matrix.tail_cons]
  unfold Dp; ring

/-- `Dp a b c = 0` exactly when `a, b, c` are collinear (Mathlib's `Collinear`). -/
theorem Dp_eq_zero_iff_collinear (a b c : ℂ) : Dp a b c = 0 ↔ Collinear ℝ ({a, b, c} : Set ℂ) := by
  rw [collinear_iff_of_mem (p₀ := a) (by simp)]
  constructor
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    by_cases hab : b = a
    · exact ⟨c - a, ⟨0, by simp⟩, ⟨0, by simp [hab]⟩, ⟨1, by simp⟩⟩
    · have hn : (b.re - a.re) ^ 2 + (b.im - a.im) ^ 2 ≠ 0 := by
        intro h0
        apply hab
        have e1 : b.re - a.re = 0 := by nlinarith [sq_nonneg (b.re - a.re), sq_nonneg (b.im - a.im)]
        have e2 : b.im - a.im = 0 := by nlinarith [sq_nonneg (b.re - a.re), sq_nonneg (b.im - a.im)]
        apply Complex.ext <;> linarith
      refine ⟨b - a, ⟨0, by simp⟩, ⟨1, by simp⟩, ⟨((c.re - a.re) * (b.re - a.re) +
        (c.im - a.im) * (b.im - a.im)) / ((b.re - a.re) ^ 2 + (b.im - a.im) ^ 2), ?_⟩⟩
      have key : ((c.re - a.re) * (b.re - a.re) + (c.im - a.im) * (b.im - a.im)) /
          ((b.re - a.re) ^ 2 + (b.im - a.im) ^ 2) * ((b.re - a.re) ^ 2 + (b.im - a.im) ^ 2) =
          (c.re - a.re) * (b.re - a.re) + (c.im - a.im) * (b.im - a.im) := div_mul_cancel₀ _ hn
      unfold Dp at h
      apply Complex.ext
      · simp only [vadd_eq_add, Complex.add_re, Complex.smul_re, Complex.sub_re, smul_eq_mul]
        apply mul_right_cancel₀ hn
        linear_combination (a.re - b.re) * key + (b.im - a.im) * h
      · simp only [vadd_eq_add, Complex.add_im, Complex.smul_im, Complex.sub_im, smul_eq_mul]
        apply mul_right_cancel₀ hn
        linear_combination (a.im - b.im) * key + (a.re - b.re) * h
  · rintro ⟨v, hv⟩
    obtain ⟨rb, hb⟩ := hv b (by simp)
    obtain ⟨rc, hc⟩ := hv c (by simp)
    have hb1 : b.re = rb * v.re + a.re := by rw [hb]; simp
    have hb2 : b.im = rb * v.im + a.im := by rw [hb]; simp
    have hc1 : c.re = rc * v.re + a.re := by rw [hc]; simp
    have hc2 : c.im = rc * v.im + a.im := by rw [hc]; simp
    unfold Dp
    rw [hb1, hb2, hc1, hc2]
    ring

/-- `Q` is the concyclicity determinant `det [x, y, x² + y², 1]` of the four points. -/
theorem Q_eq_det (a b c d : ℂ) : Q a b c d =
    Matrix.det !![a.re, a.im, a.re ^ 2 + a.im ^ 2, 1; b.re, b.im, b.re ^ 2 + b.im ^ 2, 1;
      c.re, c.im, c.re ^ 2 + c.im ^ 2, 1; d.re, d.im, d.re ^ 2 + d.im ^ 2, 1] := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_fin_three]
  simp [Matrix.submatrix, Fin.succAbove, Fin.lt_def, Q]
  ring

/-- `Q P R S M` is `Dp P R S` times the power of `M` (Mathlib's `Sphere.power`) with respect to
any circle through `P, R, S`. -/
theorem Q_eq_Dp_mul_power {P R S M O : ℂ} (hR : dist R O = dist P O) (hS : dist S O = dist P O) :
    Q P R S M = Dp P R S * (⟨O, dist P O⟩ : Sphere ℂ).power M := by
  have gP := dist_sq_re_im P O
  have gR := dist_sq_re_im R O
  have gS := dist_sq_re_im S O
  rw [hR] at gR; rw [hS] at gS
  simp only [Sphere.power]
  rw [dist_sq_re_im M O]
  unfold Q Dp
  linear_combination
    (-(R.re * S.im - R.re * M.im - R.im * S.re + R.im * M.re + S.re * M.im - S.im * M.re)) * gP -
    (-P.re * S.im + P.re * M.im + P.im * S.re - P.im * M.re - S.re * M.im + S.im * M.re) * gR -
    (P.re * R.im - P.re * M.im - P.im * R.re + P.im * M.re + R.re * M.im - R.im * M.re) * gS

/-! ### The frame coefficients of `Miquel.Coeffs`

Frame (as in `Miquel.bridge`): `A = (a1, a2)`, `B = A + w`, `C = A + c`, `F = A + n w`,
`E = A + t c`, `D = B + u (c - w)`, test point `M = F + (x, y)`. -/

/-- `al1` is the orientation `Dp A E F`: it vanishes iff `A, E, F` are collinear. -/
theorem al1_eq_zero_iff_collinear {a1 a2 w1 w2 c1 c2 n t u : ℝ} {A E F : ℂ} (hA1 : A.re = a1) (hA2 : A.im = a2) (hE1 : E.re = a1 + t * c1) (hE2 : E.im = a2 + t * c2) (hF1 : F.re = a1 + n * w1) (hF2 : F.im = a2 + n * w2) : al1 w1 w2 c1 c2 n t u = 0 ↔
    Collinear ℝ ({A, E, F} : Set ℂ) := by
  have e : Dp A E F = al1 w1 w2 c1 c2 n t u := by
    simp only [Dp, al1, hA1, hA2, hE1, hE2, hF1, hF2]
    ring
  rw [← e, Dp_eq_zero_iff_collinear]

/-- `lx1` is `2 al1` times the x-coordinate of `F` minus that of the centre `O` of the circle `(AEF)`. -/
theorem lx1_spec {a1 a2 w1 w2 c1 c2 n t u : ℝ} {A E F O : ℂ} (hA1 : A.re = a1) (hA2 : A.im = a2) (hE1 : E.re = a1 + t * c1) (hE2 : E.im = a2 + t * c2) (hF1 : F.re = a1 + n * w1) (hF2 : F.im = a2 + n * w2) (hEO : dist E O = dist A O) (hFO : dist F O = dist A O) : lx1 w1 w2 c1 c2 n t u =
    2 * al1 w1 w2 c1 c2 n t u * (F.re - O.re) := by
  have g0 := dist_sq_re_im A O
  have g1 := dist_sq_re_im E O
  have g2 := dist_sq_re_im F O
  rw [hEO] at g1; rw [hFO] at g2
  rw [hA1, hA2] at g0; rw [hE1, hE2] at g1; rw [hF1, hF2] at g2; rw [hF1]
  unfold lx1 al1
  linear_combination (n * w2) * (g0 - g1) + (-c2 * t) * (g0 - g2)

/-- `ly1` is `2 al1` times the y-coordinate of `F` minus that of the centre `O` of the circle `(AEF)`. -/
theorem ly1_spec {a1 a2 w1 w2 c1 c2 n t u : ℝ} {A E F O : ℂ} (hA1 : A.re = a1) (hA2 : A.im = a2) (hE1 : E.re = a1 + t * c1) (hE2 : E.im = a2 + t * c2) (hF1 : F.re = a1 + n * w1) (hF2 : F.im = a2 + n * w2) (hEO : dist E O = dist A O) (hFO : dist F O = dist A O) : ly1 w1 w2 c1 c2 n t u =
    2 * al1 w1 w2 c1 c2 n t u * (F.im - O.im) := by
  have g0 := dist_sq_re_im A O
  have g1 := dist_sq_re_im E O
  have g2 := dist_sq_re_im F O
  rw [hEO] at g1; rw [hFO] at g2
  rw [hA1, hA2] at g0; rw [hE1, hE2] at g1; rw [hF1, hF2] at g2; rw [hF2]
  unfold ly1 al1
  linear_combination (-n * w1) * (g0 - g1) + (c1 * t) * (g0 - g2)

/-- `al2` is the orientation `Dp B F D`: it vanishes iff `B, F, D` are collinear. -/
theorem al2_eq_zero_iff_collinear {a1 a2 w1 w2 c1 c2 n t u : ℝ} {B D F : ℂ} (hB1 : B.re = a1 + w1) (hB2 : B.im = a2 + w2) (hD1 : D.re = a1 + w1 + u * (c1 - w1)) (hD2 : D.im = a2 + w2 + u * (c2 - w2)) (hF1 : F.re = a1 + n * w1) (hF2 : F.im = a2 + n * w2) : al2 w1 w2 c1 c2 n t u = 0 ↔
    Collinear ℝ ({B, F, D} : Set ℂ) := by
  have e : Dp B F D = al2 w1 w2 c1 c2 n t u := by
    simp only [Dp, al2, hB1, hB2, hD1, hD2, hF1, hF2]
    ring
  rw [← e, Dp_eq_zero_iff_collinear]

/-- `lx2` is `2 al2` times the x-coordinate of `F` minus that of the centre `O` of the circle `(BFD)`. -/
theorem lx2_spec {a1 a2 w1 w2 c1 c2 n t u : ℝ} {B D F O : ℂ} (hB1 : B.re = a1 + w1) (hB2 : B.im = a2 + w2) (hD1 : D.re = a1 + w1 + u * (c1 - w1)) (hD2 : D.im = a2 + w2 + u * (c2 - w2)) (hF1 : F.re = a1 + n * w1) (hF2 : F.im = a2 + n * w2) (hFO : dist F O = dist B O) (hDO : dist D O = dist B O) : lx2 w1 w2 c1 c2 n t u =
    2 * al2 w1 w2 c1 c2 n t u * (F.re - O.re) := by
  have g0 := dist_sq_re_im B O
  have g1 := dist_sq_re_im F O
  have g2 := dist_sq_re_im D O
  rw [hFO] at g1; rw [hDO] at g2
  rw [hB1, hB2] at g0; rw [hF1, hF2] at g1; rw [hD1, hD2] at g2; rw [hF1]
  unfold lx2 al2
  linear_combination (-u * (-c2 + w2)) * (g0 - g1) + (-w2 * (n - 1)) * (g0 - g2)

/-- `ly2` is `2 al2` times the y-coordinate of `F` minus that of the centre `O` of the circle `(BFD)`. -/
theorem ly2_spec {a1 a2 w1 w2 c1 c2 n t u : ℝ} {B D F O : ℂ} (hB1 : B.re = a1 + w1) (hB2 : B.im = a2 + w2) (hD1 : D.re = a1 + w1 + u * (c1 - w1)) (hD2 : D.im = a2 + w2 + u * (c2 - w2)) (hF1 : F.re = a1 + n * w1) (hF2 : F.im = a2 + n * w2) (hFO : dist F O = dist B O) (hDO : dist D O = dist B O) : ly2 w1 w2 c1 c2 n t u =
    2 * al2 w1 w2 c1 c2 n t u * (F.im - O.im) := by
  have g0 := dist_sq_re_im B O
  have g1 := dist_sq_re_im F O
  have g2 := dist_sq_re_im D O
  rw [hFO] at g1; rw [hDO] at g2
  rw [hB1, hB2] at g0; rw [hF1, hF2] at g1; rw [hD1, hD2] at g2; rw [hF2]
  unfold ly2 al2
  linear_combination (u * (-c1 + w1)) * (g0 - g1) + (w1 * (n - 1)) * (g0 - g2)

/-- `al3` is the orientation `Dp C D E`: it vanishes iff `C, D, E` are collinear. -/
theorem al3_eq_zero_iff_collinear {a1 a2 w1 w2 c1 c2 n t u : ℝ} {C D E : ℂ} (hC1 : C.re = a1 + c1) (hC2 : C.im = a2 + c2) (hD1 : D.re = a1 + w1 + u * (c1 - w1)) (hD2 : D.im = a2 + w2 + u * (c2 - w2)) (hE1 : E.re = a1 + t * c1) (hE2 : E.im = a2 + t * c2) : al3 w1 w2 c1 c2 n t u = 0 ↔
    Collinear ℝ ({C, D, E} : Set ℂ) := by
  have e : Dp C D E = al3 w1 w2 c1 c2 n t u := by
    simp only [Dp, al3, hC1, hC2, hD1, hD2, hE1, hE2]
    ring
  rw [← e, Dp_eq_zero_iff_collinear]

/-- `lx3` is `2 al3` times the x-coordinate of `F` minus that of the centre `O` of the circle `(CDE)`. -/
theorem lx3_spec {a1 a2 w1 w2 c1 c2 n t u : ℝ} {C D E F O : ℂ} (hC1 : C.re = a1 + c1) (hC2 : C.im = a2 + c2) (hD1 : D.re = a1 + w1 + u * (c1 - w1)) (hD2 : D.im = a2 + w2 + u * (c2 - w2)) (hE1 : E.re = a1 + t * c1) (hE2 : E.im = a2 + t * c2) (hF1 : F.re = a1 + n * w1) (hDO : dist D O = dist C O) (hEO : dist E O = dist C O) : lx3 w1 w2 c1 c2 n t u =
    2 * al3 w1 w2 c1 c2 n t u * (F.re - O.re) := by
  have g0 := dist_sq_re_im C O
  have g1 := dist_sq_re_im D O
  have g2 := dist_sq_re_im E O
  rw [hDO] at g1; rw [hEO] at g2
  rw [hC1, hC2] at g0; rw [hD1, hD2] at g1; rw [hE1, hE2] at g2; rw [hF1]
  unfold lx3 al3
  linear_combination (c2 * (t - 1)) * (g0 - g1) + ((-c2 + w2) * (u - 1)) * (g0 - g2)

/-- `ly3` is `2 al3` times the y-coordinate of `F` minus that of the centre `O` of the circle `(CDE)`. -/
theorem ly3_spec {a1 a2 w1 w2 c1 c2 n t u : ℝ} {C D E F O : ℂ} (hC1 : C.re = a1 + c1) (hC2 : C.im = a2 + c2) (hD1 : D.re = a1 + w1 + u * (c1 - w1)) (hD2 : D.im = a2 + w2 + u * (c2 - w2)) (hE1 : E.re = a1 + t * c1) (hE2 : E.im = a2 + t * c2) (hF2 : F.im = a2 + n * w2) (hDO : dist D O = dist C O) (hEO : dist E O = dist C O) : ly3 w1 w2 c1 c2 n t u =
    2 * al3 w1 w2 c1 c2 n t u * (F.im - O.im) := by
  have g0 := dist_sq_re_im C O
  have g1 := dist_sq_re_im D O
  have g2 := dist_sq_re_im E O
  rw [hDO] at g1; rw [hEO] at g2
  rw [hC1, hC2] at g0; rw [hD1, hD2] at g1; rw [hE1, hE2] at g2; rw [hF2]
  unfold ly3 al3
  linear_combination (-c1 * (t - 1)) * (g0 - g1) + (-(-c1 + w1) * (u - 1)) * (g0 - g2)

/-- `kk3` is `al3` times the power of the frame origin `F` with respect to the circle `(CDE)`. -/
theorem kk3_spec {a1 a2 w1 w2 c1 c2 n t u : ℝ} {C D E F O : ℂ} (hC1 : C.re = a1 + c1) (hC2 : C.im = a2 + c2) (hD1 : D.re = a1 + w1 + u * (c1 - w1)) (hD2 : D.im = a2 + w2 + u * (c2 - w2)) (hE1 : E.re = a1 + t * c1) (hE2 : E.im = a2 + t * c2) (hF1 : F.re = a1 + n * w1) (hF2 : F.im = a2 + n * w2) (hDO : dist D O = dist C O) (hEO : dist E O = dist C O) : kk3 w1 w2 c1 c2 n t u =
    al3 w1 w2 c1 c2 n t u * (⟨O, dist C O⟩ : Sphere ℂ).power F := by
  have gC := dist_sq_re_im C O
  have gD := dist_sq_re_im D O
  have gE := dist_sq_re_im E O
  rw [hDO] at gD; rw [hEO] at gE
  simp only [Sphere.power]
  rw [dist_sq_re_im F O]
  rw [hC1, hC2] at gC; rw [hD1, hD2] at gD; rw [hE1, hE2] at gE; rw [hF1, hF2]
  unfold kk3 al3
  linear_combination ((t - 1) * (u - 1) * (-c1 * w2 + c2 * w1)) * gC +
    (n * (t - 1) * (-c1 * w2 + c2 * w1)) * (gC - gD) + (-(n - 1) * (u - 1) * (-c1 * w2 + c2 * w1)) * (gC - gE)

/-- `q1 x y` is `al1` times the power of the test point `M = F + (x, y)` with respect to the circle `(AEF)`; so it vanishes iff `M` lies on that circle (when `al1 ≠ 0`). -/
theorem q1_spec {a1 a2 w1 w2 c1 c2 n t u : ℝ} {x y : ℝ} {A E F M O : ℂ} (hA1 : A.re = a1) (hA2 : A.im = a2) (hE1 : E.re = a1 + t * c1) (hE2 : E.im = a2 + t * c2) (hF1 : F.re = a1 + n * w1) (hF2 : F.im = a2 + n * w2) (hM1 : M.re = a1 + n * w1 + x) (hM2 : M.im = a2 + n * w2 + y) (hEO : dist E O = dist A O) (hFO : dist F O = dist A O) : q1 w1 w2 c1 c2 n t u x y =
    al1 w1 w2 c1 c2 n t u * (⟨O, dist A O⟩ : Sphere ℂ).power M := by
  have e1 : Q A E F M = q1 w1 w2 c1 c2 n t u x y := by
    simp only [Q, q1, al1, lx1, ly1, hA1, hA2, hE1, hE2, hF1, hF2, hM1, hM2]
    ring
  have e2 : Dp A E F = al1 w1 w2 c1 c2 n t u := by
    simp only [Dp, al1, hA1, hA2, hE1, hE2, hF1, hF2]
    ring
  rw [← e1, ← e2, Q_eq_Dp_mul_power hEO hFO]

/-- `q2 x y` is `al2` times the power of the test point `M = F + (x, y)` with respect to the circle `(BFD)`; so it vanishes iff `M` lies on that circle (when `al2 ≠ 0`). -/
theorem q2_spec {a1 a2 w1 w2 c1 c2 n t u : ℝ} {x y : ℝ} {B D F M O : ℂ} (hB1 : B.re = a1 + w1) (hB2 : B.im = a2 + w2) (hD1 : D.re = a1 + w1 + u * (c1 - w1)) (hD2 : D.im = a2 + w2 + u * (c2 - w2)) (hF1 : F.re = a1 + n * w1) (hF2 : F.im = a2 + n * w2) (hM1 : M.re = a1 + n * w1 + x) (hM2 : M.im = a2 + n * w2 + y) (hFO : dist F O = dist B O) (hDO : dist D O = dist B O) : q2 w1 w2 c1 c2 n t u x y =
    al2 w1 w2 c1 c2 n t u * (⟨O, dist B O⟩ : Sphere ℂ).power M := by
  have e1 : Q B F D M = q2 w1 w2 c1 c2 n t u x y := by
    simp only [Q, q2, al2, lx2, ly2, hB1, hB2, hD1, hD2, hF1, hF2, hM1, hM2]
    ring
  have e2 : Dp B F D = al2 w1 w2 c1 c2 n t u := by
    simp only [Dp, al2, hB1, hB2, hD1, hD2, hF1, hF2]
    ring
  rw [← e1, ← e2, Q_eq_Dp_mul_power hFO hDO]

/-- `q3 x y` is `al3` times the power of the test point `M = F + (x, y)` with respect to the circle `(CDE)`; so it vanishes iff `M` lies on that circle (when `al3 ≠ 0`). -/
theorem q3_spec {a1 a2 w1 w2 c1 c2 n t u : ℝ} {x y : ℝ} {C D E M O : ℂ} (hC1 : C.re = a1 + c1) (hC2 : C.im = a2 + c2) (hD1 : D.re = a1 + w1 + u * (c1 - w1)) (hD2 : D.im = a2 + w2 + u * (c2 - w2)) (hE1 : E.re = a1 + t * c1) (hE2 : E.im = a2 + t * c2) (hM1 : M.re = a1 + n * w1 + x) (hM2 : M.im = a2 + n * w2 + y) (hDO : dist D O = dist C O) (hEO : dist E O = dist C O) : q3 w1 w2 c1 c2 n t u x y =
    al3 w1 w2 c1 c2 n t u * (⟨O, dist C O⟩ : Sphere ℂ).power M := by
  have e1 : Q C D E M = q3 w1 w2 c1 c2 n t u x y := by
    simp only [Q, q3, al3, lx3, ly3, kk3, hC1, hC2, hD1, hD2, hE1, hE2, hM1, hM2]
    ring
  have e2 : Dp C D E = al3 w1 w2 c1 c2 n t u := by
    simp only [Dp, al3, hC1, hC2, hD1, hD2, hE1, hE2]
    ring
  rw [← e1, ← e2, Q_eq_Dp_mul_power hDO hEO]

/-- `KK = n t u (n - 1) |AB|²`. -/
theorem KK_eq_dist_sq {a1 a2 w1 w2 c1 c2 n t u : ℝ} {A B : ℂ} (hA1 : A.re = a1) (hA2 : A.im = a2) (hB1 : B.re = a1 + w1) (hB2 : B.im = a2 + w2) : KK w1 w2 c1 c2 n t u =
    n * t * u * (n - 1) * dist A B ^ 2 := by
  rw [dist_sq_re_im, hA1, hA2, hB1, hB2]
  unfold KK; ring

/-! ### Certificate multipliers

These have no standard meaning; the bridges record their role: on one circle, `K x q3`
(resp. `K y q3`) is the multiplier times the polynomial of the other circle. -/

/-- On the circle `q2 = 0`, `certx1` is the multiplier of `q1` in `K x q3`. -/
theorem certx1_spec {w1 w2 c1 c2 n t u x y : ℝ} (h : q2 w1 w2 c1 c2 n t u x y = 0) : KK w1 w2 c1 c2 n t u * x * q3 w1 w2 c1 c2 n t u x y = certx1 w1 w2 c1 c2 n t u x y * q1 w1 w2 c1 c2 n t u x y := by
  rw [cert_x, h]
  ring

/-- On the circle `q1 = 0`, `certx2` is the multiplier of `q2` in `K x q3`. -/
theorem certx2_spec {w1 w2 c1 c2 n t u x y : ℝ} (h : q1 w1 w2 c1 c2 n t u x y = 0) : KK w1 w2 c1 c2 n t u * x * q3 w1 w2 c1 c2 n t u x y = certx2 w1 w2 c1 c2 n t u x y * q2 w1 w2 c1 c2 n t u x y := by
  rw [cert_x, h]
  ring

/-- On the circle `q2 = 0`, `certy1` is the multiplier of `q1` in `K y q3`. -/
theorem certy1_spec {w1 w2 c1 c2 n t u x y : ℝ} (h : q2 w1 w2 c1 c2 n t u x y = 0) : KK w1 w2 c1 c2 n t u * y * q3 w1 w2 c1 c2 n t u x y = certy1 w1 w2 c1 c2 n t u x y * q1 w1 w2 c1 c2 n t u x y := by
  rw [cert_y, h]
  ring

/-- On the circle `q1 = 0`, `certy2` is the multiplier of `q2` in `K y q3`. -/
theorem certy2_spec {w1 w2 c1 c2 n t u x y : ℝ} (h : q1 w1 w2 c1 c2 n t u x y = 0) : KK w1 w2 c1 c2 n t u * y * q3 w1 w2 c1 c2 n t u x y = certy2 w1 w2 c1 c2 n t u x y * q2 w1 w2 c1 c2 n t u x y := by
  rw [cert_y, h]
  ring

/-! ### Circumcentre coordinates -/

/-- Any point `O` equidistant from `P, R, S` satisfies `O.re · 2 Dp P R S = circX …`; with
`exists_circle` this says `circX / (2 Dp)` is the x-coordinate of the circumcentre. -/
theorem circX_spec {P R S O : ℂ} (hR : dist R O = dist P O) (hS : dist S O = dist P O) :
    O.re * (2 * Dp P R S) = circX P.re P.im R.re R.im S.re S.im := by
  have gP := dist_sq_re_im P O
  have gR := dist_sq_re_im R O
  have gS := dist_sq_re_im S O
  rw [hR] at gR; rw [hS] at gS
  unfold circX Dp
  linear_combination (S.im - P.im) * (gP - gR) - (R.im - P.im) * (gP - gS)

/-- Any point `O` equidistant from `P, R, S` satisfies `O.im · 2 Dp P R S = circY …`. -/
theorem circY_spec {P R S O : ℂ} (hR : dist R O = dist P O) (hS : dist S O = dist P O) :
    O.im * (2 * Dp P R S) = circY P.re P.im R.re R.im S.re S.im := by
  have gP := dist_sq_re_im P O
  have gR := dist_sq_re_im R O
  have gS := dist_sq_re_im S O
  rw [hR] at gR; rw [hS] at gS
  unfold circY Dp
  linear_combination (-(S.re - P.re)) * (gP - gR) + (R.re - P.re) * (gP - gS)

/-! ### The radical-axis point -/

/-- `rpN = 0` iff the two circle polynomials are proportional (`a₂ f₁ = a₁ f₂`), i.e. the radical axis is undefined. -/
theorem rpN_eq_zero_iff (a1 b1 c1 a2 b2 c2 : ℝ) : rpN a1 b1 c1 a2 b2 c2 = 0 ↔
    ∀ x y : ℝ, a2 * (a1 * (x ^ 2 + y ^ 2) + b1 * x + c1 * y) =
      a1 * (a2 * (x ^ 2 + y ^ 2) + b2 * x + c2 * y) := by
  unfold rpN
  constructor
  · intro h x y
    have h1 : a2 * b1 - a1 * b2 = 0 := by nlinarith [sq_nonneg (a2 * b1 - a1 * b2), sq_nonneg (a2 * c1 - a1 * c2)]
    have h2 : a2 * c1 - a1 * c2 = 0 := by nlinarith [sq_nonneg (a2 * b1 - a1 * b2), sq_nonneg (a2 * c1 - a1 * c2)]
    linear_combination x * h1 + y * h2
  · intro h
    have h1 := h 1 0
    have h2 := h 0 1
    have e1 : a2 * b1 - a1 * b2 = 0 := by linear_combination h1
    have e2 : a2 * c1 - a1 * c2 = 0 := by linear_combination h2
    rw [e1, e2]; ring

/-- `(rpx, rpy)` is the second intersection point: every common zero of the two circle polynomials (both through the origin) is the origin or `(rpx, rpy)`. -/
theorem rpx_rpy_spec {a1 b1 c1 a2 b2 c2 x y : ℝ} (hN : rpN a1 b1 c1 a2 b2 c2 ≠ 0) : a1 * (x ^ 2 + y ^ 2) + b1 * x + c1 * y = 0 → a2 * (x ^ 2 + y ^ 2) + b2 * x + c2 * y = 0 →
    (x = 0 ∧ y = 0) ∨ (x = rpx a1 b1 c1 a2 b2 c2 ∧ y = rpy a1 b1 c1 a2 b2 c2) := by
  intro h1 h2
  have hNe : rpN a1 b1 c1 a2 b2 c2 = ((a2 * b1 - a1 * b2) ^ 2 + (a2 * c1 - a1 * c2) ^ 2) := rfl
  have hL : ((a2 * b1 - a1 * b2) * x + (a2 * c1 - a1 * c2) * y) = 0 := by linear_combination a2 * h1 - a1 * h2
  have hx : rpN a1 b1 c1 a2 b2 c2 * x = (a2 * c1 - a1 * c2) * ((a2 * c1 - a1 * c2) * x - (a2 * b1 - a1 * b2) * y) := by
    rw [hNe]; linear_combination (a2 * b1 - a1 * b2) * hL
  have hy : rpN a1 b1 c1 a2 b2 c2 * y = -(a2 * b1 - a1 * b2) * ((a2 * c1 - a1 * c2) * x - (a2 * b1 - a1 * b2) * y) := by
    rw [hNe]; linear_combination (a2 * c1 - a1 * c2) * hL
  have hm : rpN a1 b1 c1 a2 b2 c2 * (((a2 * c1 - a1 * c2) * x - (a2 * b1 - a1 * b2) * y) * (((a2 * c1 - a1 * c2) * x - (a2 * b1 - a1 * b2) * y) - (b1 * c2 - c1 * b2))) = 0 := by
    rw [hNe]; linear_combination (-((a2 * b1 - a1 * b2) * b2 + (a2 * c1 - a1 * c2) * c2) * ((a2 * b1 - a1 * b2) ^ 2 + (a2 * c1 - a1 * c2) ^ 2) + (-((a2 * b1 - a1 * b2) * b1 + (a2 * c1 - a1 * c2) * c1) * (a2 * ((a2 * b1 - a1 * b2) * x + (a2 * c1 - a1 * c2) * y) + b2 * (a2 * b1 - a1 * b2) + c2 * (a2 * c1 - a1 * c2)) + ((a2 * b1 - a1 * b2) * b2 + (a2 * c1 - a1 * c2) * c2) * (a1 * ((a2 * b1 - a1 * b2) * x + (a2 * c1 - a1 * c2) * y) + b1 * (a2 * b1 - a1 * b2) + c1 * (a2 * c1 - a1 * c2))) * a2) * h1 + (((a2 * b1 - a1 * b2) * b1 + (a2 * c1 - a1 * c2) * c1) * ((a2 * b1 - a1 * b2) ^ 2 + (a2 * c1 - a1 * c2) ^ 2) - (-((a2 * b1 - a1 * b2) * b1 + (a2 * c1 - a1 * c2) * c1) * (a2 * ((a2 * b1 - a1 * b2) * x + (a2 * c1 - a1 * c2) * y) + b2 * (a2 * b1 - a1 * b2) + c2 * (a2 * c1 - a1 * c2)) + ((a2 * b1 - a1 * b2) * b2 + (a2 * c1 - a1 * c2) * c2) * (a1 * ((a2 * b1 - a1 * b2) * x + (a2 * c1 - a1 * c2) * y) + b1 * (a2 * b1 - a1 * b2) + c1 * (a2 * c1 - a1 * c2))) * a1) * h2
  rcases mul_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hN) with h0 | hD
  · left
    rw [h0, mul_zero] at hx
    rw [h0, mul_zero] at hy
    exact ⟨(mul_eq_zero.mp hx).resolve_left hN, (mul_eq_zero.mp hy).resolve_left hN⟩
  · right
    have hD' : ((a2 * c1 - a1 * c2) * x - (a2 * b1 - a1 * b2) * y) = (b1 * c2 - c1 * b2) := by linear_combination hD
    rw [hD'] at hx hy
    unfold rpx rpy
    constructor
    · rw [eq_div_iff hN]; linear_combination hx
    · rw [eq_div_iff hN]; linear_combination hy

end Miquel
