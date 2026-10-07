import Mathlib

/-!
# Miquel's theorem — the concyclicity determinant

The Euclidean plane is modelled as `ℂ`. For four points `a b c d`, `Q a b c d` is the
concyclicity determinant `det [x, y, x²+y², 1]` (expanded along the third column); it vanishes
iff `a b c d` are concyclic or collinear.

Main results of this file:
* `Q_eq_zero_of_dist` : four points on a common circle have `Q = 0`;
* `Q_swap12`, `Q_swap34` : `Q` is antisymmetric under the first and last transpositions.
-/

noncomputable section

namespace Miquel

open Complex

/-- Concyclicity determinant `det [x, y, x²+y², 1]` of four points, expanded along the third
column. Vanishes iff the points are concyclic or collinear. -/
def Q (a b c d : ℂ) : ℝ :=
  (b.re * c.im - b.re * d.im - b.im * c.re + b.im * d.re + c.re * d.im - c.im * d.re) *
      (a.re ^ 2 + a.im ^ 2) +
    (-a.re * c.im + a.re * d.im + a.im * c.re - a.im * d.re - c.re * d.im + c.im * d.re) *
      (b.re ^ 2 + b.im ^ 2) +
    (a.re * b.im - a.re * d.im - a.im * b.re + a.im * d.re + b.re * d.im - b.im * d.re) *
      (c.re ^ 2 + c.im ^ 2) +
    (-a.re * b.im + a.re * c.im + a.im * b.re - a.im * c.re - b.re * c.im + b.im * c.re) *
      (d.re ^ 2 + d.im ^ 2)

lemma dist_sq_re_im (z w : ℂ) : dist z w ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
  rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity)]

/-- If four points lie on a common circle, the concyclicity determinant vanishes. -/
lemma Q_eq_zero_of_dist {a b c d o : ℂ} {r : ℝ}
    (ha : dist a o = r) (hb : dist b o = r) (hc : dist c o = r) (hd : dist d o = r) :
    Q a b c d = 0 := by
  have ga := dist_sq_re_im a o
  have gb := dist_sq_re_im b o
  have gc := dist_sq_re_im c o
  have gd := dist_sq_re_im d o
  rw [ha] at ga; rw [hb] at gb; rw [hc] at gc; rw [hd] at gd
  unfold Q
  linear_combination
    (-(b.re * c.im - b.re * d.im - b.im * c.re + b.im * d.re + c.re * d.im - c.im * d.re)) * ga -
    (-a.re * c.im + a.re * d.im + a.im * c.re - a.im * d.re - c.re * d.im + c.im * d.re) * gb -
    (a.re * b.im - a.re * d.im - a.im * b.re + a.im * d.re + b.re * d.im - b.im * d.re) * gc -
    (-a.re * b.im + a.re * c.im + a.im * b.re - a.im * c.re - b.re * c.im + b.im * c.re) * gd

/-- `Q` is antisymmetric in its first two arguments. -/
lemma Q_swap12 (a b c d : ℂ) : Q b a c d = -Q a b c d := by
  unfold Q; ring

/-- `Q` is antisymmetric in its last two arguments. -/
lemma Q_swap34 (a b c d : ℂ) : Q a b d c = -Q a b c d := by
  unfold Q; ring

/-- `Q` vanishes on a repeated point. -/
lemma Q_self (a b c : ℂ) : Q a a b c = 0 := by
  unfold Q; ring

end Miquel
