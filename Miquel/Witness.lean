import Miquel.Main

/-!
# Non-vacuity witnesses

For each theorem of the development with nontrivial hypotheses, a concrete instance at which all
of its hypotheses hold (proved below), so none of these statements is vacuous.

* `miquel`, `miquel_concyclic`: the triangle `A = 0`, `B = 4`, `C = 1 + 3i` with the side
  midpoints `F = 2`, `E = 1/2 + 3/2 i`, `D = 5/2 + 3/2 i` (`n = t = u = 1/2`) —
  `miquel_hyps_example`; `miquel_example` (in `Miquel.Main`) instantiates the conclusion of
  `miquel_concyclic`, `miquel_point_example` that of `miquel`.
* `dist_eq_of_Q_eq_zero`: the circle of radius 5 about `0` through `5, 5i, -5` and `3 + 4i`.
* `circ_aux`: the points `(0,0), (2,0), (0,2)` with circumcentre `(1,1)`.
* `bridge`: the same Miquel configuration, in the frame at `A = 0`.
* `core`: the circles `x² + y² - 2x`, `x² + y² - 2y` (meeting at `0` and `(1,1)`) and the third
  circle `x² + y² - 2` through `(1,1)` — `core_example`; `core_example_conclusion` applies `core`.
-/

noncomputable section

namespace Miquel

open Complex

/-- All ten hypotheses of `miquel` / `miquel_concyclic` hold for the midpoint configuration. -/
theorem miquel_hyps_example :
    Dp 0 4 ⟨1, 3⟩ ≠ 0 ∧
      (2 : ℂ) = 0 + ((1 / 2 : ℝ) : ℂ) * (4 - 0) ∧
      (⟨1 / 2, 3 / 2⟩ : ℂ) = 0 + ((1 / 2 : ℝ) : ℂ) * (⟨1, 3⟩ - 0) ∧
      (⟨5 / 2, 3 / 2⟩ : ℂ) = 4 + ((1 / 2 : ℝ) : ℂ) * (⟨1, 3⟩ - 4) ∧
      (1 / 2 : ℝ) ≠ 0 ∧ (1 / 2 : ℝ) ≠ 1 ∧ (1 / 2 : ℝ) ≠ 0 ∧ (1 / 2 : ℝ) ≠ 1 ∧
      (1 / 2 : ℝ) ≠ 0 ∧ (1 / 2 : ℝ) ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold Dp; norm_num
  · apply Complex.ext <;> norm_num
  · apply Complex.ext <;> norm_num
  · apply Complex.ext <;> norm_num
  · norm_num

/-- `miquel` instantiated at the midpoint configuration: a Miquel point exists there. -/
theorem miquel_point_example :
    ∃ M : ℂ,
      (∀ (O : ℂ) (r : ℝ), dist 0 O = r → dist (⟨1 / 2, 3 / 2⟩ : ℂ) O = r → dist (2 : ℂ) O = r →
        dist M O = r) ∧
      (∀ (O : ℂ) (r : ℝ), dist 4 O = r → dist (2 : ℂ) O = r → dist (⟨5 / 2, 3 / 2⟩ : ℂ) O = r →
        dist M O = r) ∧
      (∀ (O : ℂ) (r : ℝ), dist (⟨1, 3⟩ : ℂ) O = r → dist (⟨5 / 2, 3 / 2⟩ : ℂ) O = r →
        dist (⟨1 / 2, 3 / 2⟩ : ℂ) O = r → dist M O = r) := by
  obtain ⟨h0, hF, hE, hD, hn0, hn1, ht0, ht1, hu0, hu1⟩ := miquel_hyps_example
  exact miquel h0 hF hE hD hn0 hn1 ht0 ht1 hu0 hu1

lemma dist_eq_five {z : ℂ} (h : z.re ^ 2 + z.im ^ 2 = 25) : dist z 0 = 5 := by
  rw [← pow_left_inj₀ dist_nonneg (by norm_num : (0 : ℝ) ≤ 5) two_ne_zero, dist_sq_re_im]
  simp only [Complex.zero_re, Complex.zero_im, sub_zero]; rw [h]; norm_num

/-- The hypotheses of `dist_eq_of_Q_eq_zero` hold for `5, 5i, -5`, `M = 3 + 4i` on the circle
of radius `5` about `0`; the conclusion follows. -/
theorem dist_eq_of_Q_eq_zero_example :
    Dp 5 ⟨0, 5⟩ (-5) ≠ 0 ∧ dist (5 : ℂ) 0 = 5 ∧ dist (⟨0, 5⟩ : ℂ) 0 = 5 ∧
      dist (-5 : ℂ) 0 = 5 ∧ Q 5 ⟨0, 5⟩ (-5) ⟨3, 4⟩ = 0 ∧ dist (⟨3, 4⟩ : ℂ) 0 = 5 := by
  have h1 : Dp 5 ⟨0, 5⟩ (-5) ≠ 0 := by unfold Dp; norm_num
  have h2 : dist (5 : ℂ) 0 = 5 := dist_eq_five (by norm_num)
  have h3 : dist (⟨0, 5⟩ : ℂ) 0 = 5 := dist_eq_five (by norm_num)
  have h4 : dist (-5 : ℂ) 0 = 5 := dist_eq_five (by norm_num)
  have h5 : Q 5 ⟨0, 5⟩ (-5) ⟨3, 4⟩ = 0 := by unfold Q; norm_num
  exact ⟨h1, h2, h3, h4, h5, dist_eq_of_Q_eq_zero h1 h2 h3 h4 h5⟩

/-- The hypotheses of `circ_aux` hold for `p = (0,0)`, `r = (2,0)`, `s = (0,2)`, `d = -4`,
circumcentre `(1,1)`; the conclusion follows. -/
theorem circ_aux_example :
    ((-4 : ℝ) = -0 * 0 + 0 * 2 + 0 * 2 - 0 * 0 - 2 * 2 + 0 * 0) ∧ (-4 : ℝ) ≠ 0 ∧
      (1 : ℝ) * (2 * -4) = circX 0 0 2 0 0 2 ∧ (1 : ℝ) * (2 * -4) = circY 0 0 2 0 0 2 ∧
      ((2 : ℝ) - 1) ^ 2 + (0 - 1) ^ 2 = (0 - 1) ^ 2 + (0 - 1) ^ 2 := by
  have hd : (-4 : ℝ) = -0 * 0 + 0 * 2 + 0 * 2 - 0 * 0 - 2 * 2 + 0 * 0 := by norm_num
  have hD : (-4 : ℝ) ≠ 0 := by norm_num
  have hx : (1 : ℝ) * (2 * -4) = circX 0 0 2 0 0 2 := by unfold circX; norm_num
  have hy : (1 : ℝ) * (2 * -4) = circY 0 0 2 0 0 2 := by unfold circY; norm_num
  exact ⟨hd, hD, hx, hy, (circ_aux hd hD hx hy).1⟩

/-- The hypotheses of `bridge` hold for the midpoint configuration in the frame at `A = 0`
(`w = 4`, `c = 1 + 3i`, `n = t = u = 1/2`, `M = F + (1, 1)`). -/
theorem bridge_example :
    Q 0 ⟨1 / 2, 3 / 2⟩ 2 ⟨3, 1⟩ = q1 4 0 1 3 (1 / 2) (1 / 2) (1 / 2) 1 1 ∧
      Dp 0 4 ⟨1, 3⟩ = -(-1 * 0 + 3 * 4) := by
  obtain ⟨e1, -, -, -, -, -, e0⟩ := bridge (a1 := 0) (a2 := 0) (w1 := 4) (w2 := 0) (c1 := 1)
    (c2 := 3) (n := 1 / 2) (t := 1 / 2) (u := 1 / 2) (x := 1) (y := 1) (A := 0) (B := 4)
    (C := ⟨1, 3⟩) (D := ⟨5 / 2, 3 / 2⟩) (E := ⟨1 / 2, 3 / 2⟩) (F := 2) (M := ⟨3, 1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨e1, e0⟩

/-- The hypotheses of `core` hold for a genuine configuration of three circles:
`C₁ = x² + y² - 2x` (centre `(1,0)`) and `C₂ = x² + y² - 2y` (centre `(0,1)`), both through the
origin and meeting again at `(1,1)`, and `C₃ = x² + y² - 2` (centre `0`, radius `√2`, not through
the origin), with `K = 1`, `T = -1/2` and the degree-one polynomial multipliers below. -/
theorem core_example :
    rpN 1 (-2) 0 1 0 (-2) ≠ 0 ∧ (1 : ℝ) ≠ 0 ∧
      (∀ x y : ℝ, 1 * x * (1 * (x ^ 2 + y ^ 2) + 0 * x + 0 * y + (-2)) =
        (fun x y : ℝ => (x - y) / 2 + 1) x y * (1 * (x ^ 2 + y ^ 2) + (-2) * x + 0 * y) +
          (fun x y : ℝ => (x + y) / 2) x y * (1 * (x ^ 2 + y ^ 2) + 0 * x + (-2) * y)) ∧
      (∀ x y : ℝ, 1 * y * (1 * (x ^ 2 + y ^ 2) + 0 * x + 0 * y + (-2)) =
        (fun x y : ℝ => (x + y) / 2) x y * (1 * (x ^ 2 + y ^ 2) + (-2) * x + 0 * y) +
          (fun x y : ℝ => (y - x) / 2 + 1) x y * (1 * (x ^ 2 + y ^ 2) + 0 * x + (-2) * y)) ∧
      (1 : ℝ) * (-2) = (-1 / 2) * ((-2) * (-2) - 0 * 0) := by
  refine ⟨by unfold rpN; norm_num, one_ne_zero, fun x y => by beta_reduce; ring,
    fun x y => by beta_reduce; ring, by norm_num⟩

/-- The radical-axis point of `C₁` and `C₂` in `core_example` is `(1,1)`, not the origin. -/
theorem core_example_point : rpx 1 (-2) 0 1 0 (-2) = 1 ∧ rpy 1 (-2) 0 1 0 (-2) = 1 := by
  unfold rpx rpy rpN; norm_num

/-- `core` applied to `core_example`: the second intersection point of `C₁` and `C₂` lies on
`C₃ = x² + y² - 2`. -/
theorem core_example_conclusion :
    1 * (rpx 1 (-2) 0 1 0 (-2) ^ 2 + rpy 1 (-2) 0 1 0 (-2) ^ 2) + 0 * rpx 1 (-2) 0 1 0 (-2) +
      0 * rpy 1 (-2) 0 1 0 (-2) + (-2) = 0 := by
  obtain ⟨hN, hK, hcx, hcy, ht⟩ := core_example
  exact core _ _ _ _ hN hK hcx hcy ht

end Miquel
