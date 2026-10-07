import Miquel.Frame

/-!
# Miquel's theorem

The Euclidean plane is `ℂ`. Let `A B C` be a non-degenerate triangle (`Dp A B C ≠ 0`, i.e. not
collinear) and let
* `F = A + n (B - A)` lie on line `AB`, with `F ≠ A, B` (`n ≠ 0, 1`);
* `E = A + t (C - A)` lie on line `CA`, with `E ≠ A, C` (`t ≠ 0, 1`);
* `D = B + u (C - B)` lie on line `BC`, with `D ≠ B, C` (`u ≠ 0, 1`).

Then there is a point `M` (the Miquel point) that lies on every circle through `A, E, F`, on every
circle through `B, F, D` and on every circle through `C, D, E` (`miquel`). Each of these triples
is non-collinear, so each circle exists and is unique; `miquel_concyclic` packages this as
"the three circles have a common point". The points `D, E, F` may lie on the extended sides.
-/

noncomputable section

namespace Miquel

open Complex

/-- Real part of a point on a line. -/
lemma line_re (P R : ℂ) (s : ℝ) : (P + (s : ℂ) * (R - P)).re = P.re + s * (R.re - P.re) := by
  simp

/-- Imaginary part of a point on a line. -/
lemma line_im (P R : ℂ) (s : ℝ) : (P + (s : ℂ) * (R - P)).im = P.im + s * (R.im - P.im) := by
  simp

/-- Coordinate bridge: in the frame `B = A + w`, `C = A + c`, `F = A + n w`, `E = A + t c`,
`D = B + u (c - w)`, `M = F + (x, y)`, the concyclicity determinants and orientations are the
frame polynomials of `Miquel.Coeffs`. -/
lemma bridge {a1 a2 w1 w2 c1 c2 n t u x y : ℝ} {A B C D E F M : ℂ}
    (hA1 : A.re = a1) (hA2 : A.im = a2) (hB1 : B.re = a1 + w1) (hB2 : B.im = a2 + w2)
    (hC1 : C.re = a1 + c1) (hC2 : C.im = a2 + c2)
    (hF1 : F.re = a1 + n * w1) (hF2 : F.im = a2 + n * w2)
    (hE1 : E.re = a1 + t * c1) (hE2 : E.im = a2 + t * c2)
    (hD1 : D.re = a1 + w1 + u * (c1 - w1)) (hD2 : D.im = a2 + w2 + u * (c2 - w2))
    (hM1 : M.re = a1 + n * w1 + x) (hM2 : M.im = a2 + n * w2 + y) :
    Q A E F M = q1 w1 w2 c1 c2 n t u x y ∧ Q B F D M = q2 w1 w2 c1 c2 n t u x y ∧
      Q C D E M = q3 w1 w2 c1 c2 n t u x y ∧
      Dp A E F = al1 w1 w2 c1 c2 n t u ∧ Dp B F D = al2 w1 w2 c1 c2 n t u ∧
      Dp C D E = al3 w1 w2 c1 c2 n t u ∧ Dp A B C = -(-c1 * w2 + c2 * w1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [Q, Dp, q1, q2, q3, al1, lx1, ly1, al2, lx2, ly2, al3, lx3, ly3, kk3,
      hA1, hA2, hB1, hB2, hC1, hC2, hD1, hD2, hE1, hE2, hF1, hF2, hM1, hM2]
    ring

/-- **Miquel's theorem.** For a non-degenerate triangle `A B C` and points `F` on line `AB`,
`E` on line `CA`, `D` on line `BC`, none of them a vertex, there is a point `M` lying on every
circle through `A, E, F`, every circle through `B, F, D` and every circle through `C, D, E`. -/
theorem miquel {A B C D E F : ℂ} {n t u : ℝ} (hABC : Dp A B C ≠ 0)
    (hF : F = A + (n : ℂ) * (B - A)) (hE : E = A + (t : ℂ) * (C - A))
    (hD : D = B + (u : ℂ) * (C - B))
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    ∃ M : ℂ,
      (∀ (O : ℂ) (r : ℝ), dist A O = r → dist E O = r → dist F O = r → dist M O = r) ∧
      (∀ (O : ℂ) (r : ℝ), dist B O = r → dist F O = r → dist D O = r → dist M O = r) ∧
      (∀ (O : ℂ) (r : ℝ), dist C O = r → dist D O = r → dist E O = r → dist M O = r) := by
  set w1 := B.re - A.re with hw1
  set w2 := B.im - A.im with hw2
  set c1 := C.re - A.re with hc1
  set c2 := C.im - A.im with hc2
  have hΔ : -c1 * w2 + c2 * w1 ≠ 0 := by
    intro h0; apply hABC; unfold Dp; rw [hw1, hw2, hc1, hc2] at h0; linear_combination -h0
  obtain ⟨x, y, h1, h2, h3⟩ := frame hΔ hn0 hn1 ht0 hu0
  refine ⟨⟨A.re + n * w1 + x, A.im + n * w2 + y⟩, ?_⟩
  have hF1 : F.re = A.re + n * w1 := by rw [hF, line_re]
  have hF2 : F.im = A.im + n * w2 := by rw [hF, line_im]
  have hE1 : E.re = A.re + t * c1 := by rw [hE, line_re]
  have hE2 : E.im = A.im + t * c2 := by rw [hE, line_im]
  have hD1 : D.re = A.re + w1 + u * (c1 - w1) := by
    rw [hD, line_re]; simp only [hw1, hc1]; ring
  have hD2 : D.im = A.im + w2 + u * (c2 - w2) := by
    rw [hD, line_im]; simp only [hw2, hc2]; ring
  obtain ⟨e1, e2, e3, d1, d2, d3, -⟩ := bridge (A := A) (B := B) (C := C) (D := D) (E := E)
    (F := F) (M := ⟨A.re + n * w1 + x, A.im + n * w2 + y⟩)
    rfl rfl (by rw [hw1]; ring) (by rw [hw2]; ring) (by rw [hc1]; ring) (by rw [hc2]; ring)
    hF1 hF2 hE1 hE2 hD1 hD2 rfl rfl
  have hd1 : Dp A E F ≠ 0 := by
    rw [d1]; unfold al1; exact mul_ne_zero (mul_ne_zero hn0 ht0) hΔ
  have hd2 : Dp B F D ≠ 0 := by
    rw [d2]; unfold al2
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hu0) (sub_ne_zero.mpr hn1)) hΔ
  have hd3 : Dp C D E ≠ 0 := by
    rw [d3]; unfold al3
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr ht1) (sub_ne_zero.mpr hu1)) hΔ
  refine ⟨fun O r hA hE' hF' => ?_, fun O r hB hF' hD' => ?_, fun O r hC hD' hE' => ?_⟩
  · exact dist_eq_of_Q_eq_zero hd1 hA hE' hF' (e1.trans h1)
  · exact dist_eq_of_Q_eq_zero hd2 hB hF' hD' (e2.trans h2)
  · exact dist_eq_of_Q_eq_zero hd3 hC hD' hE' (e3.trans h3)

/-- **Miquel's theorem (concyclic form).** Under the same hypotheses, the circles `(AEF)`,
`(BFD)`, `(CDE)` exist (centres `O₁ O₂ O₃`) and pass through a common point `M`. -/
theorem miquel_concyclic {A B C D E F : ℂ} {n t u : ℝ} (hABC : Dp A B C ≠ 0)
    (hF : F = A + (n : ℂ) * (B - A)) (hE : E = A + (t : ℂ) * (C - A))
    (hD : D = B + (u : ℂ) * (C - B))
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    ∃ O₁ O₂ O₃ M : ℂ,
      dist E O₁ = dist A O₁ ∧ dist F O₁ = dist A O₁ ∧ dist M O₁ = dist A O₁ ∧
      dist F O₂ = dist B O₂ ∧ dist D O₂ = dist B O₂ ∧ dist M O₂ = dist B O₂ ∧
      dist D O₃ = dist C O₃ ∧ dist E O₃ = dist C O₃ ∧ dist M O₃ = dist C O₃ := by
  obtain ⟨M, hM1, hM2, hM3⟩ := miquel hABC hF hE hD hn0 hn1 ht0 ht1 hu0 hu1
  have hΔ : Dp A B C ≠ 0 := hABC
  obtain ⟨-, -, -, d1, d2, d3, d0⟩ := bridge (a1 := A.re) (a2 := A.im)
    (w1 := B.re - A.re) (w2 := B.im - A.im) (c1 := C.re - A.re) (c2 := C.im - A.im)
    (x := 0) (y := 0) (n := n) (t := t) (u := u) (A := A) (B := B) (C := C) (D := D) (E := E)
    (F := F) (M := F) rfl rfl (by ring) (by ring)
    (by ring) (by ring) (by rw [hF, line_re]) (by rw [hF, line_im]) (by rw [hE, line_re])
    (by rw [hE, line_im]) (by rw [hD, line_re]; ring) (by rw [hD, line_im]; ring)
    (by rw [hF, line_re]; ring) (by rw [hF, line_im]; ring)
  have hΔ' : -(C.re - A.re) * (B.im - A.im) + (C.im - A.im) * (B.re - A.re) ≠ 0 := by
    intro h0; apply hΔ; rw [d0, h0, neg_zero]
  have hd1 : Dp A E F ≠ 0 := by
    rw [d1]; unfold al1; exact mul_ne_zero (mul_ne_zero hn0 ht0) hΔ'
  have hd2 : Dp B F D ≠ 0 := by
    rw [d2]; unfold al2
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hu0) (sub_ne_zero.mpr hn1)) hΔ'
  have hd3 : Dp C D E ≠ 0 := by
    rw [d3]; unfold al3
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr ht1) (sub_ne_zero.mpr hu1)) hΔ'
  obtain ⟨O₁, h1E, h1F⟩ := exists_circle hd1
  obtain ⟨O₂, h2F, h2D⟩ := exists_circle hd2
  obtain ⟨O₃, h3D, h3E⟩ := exists_circle hd3
  exact ⟨O₁, O₂, O₃, M, h1E, h1F, hM1 O₁ _ rfl h1E h1F, h2F, h2D, hM2 O₂ _ rfl h2F h2D,
    h3D, h3E, hM3 O₃ _ rfl h3D h3E⟩

/-! ### Non-vacuity and a negative control

Concrete instance: `A = 0`, `B = 4`, `C = 1 + 3i`, `D, E, F` the midpoints of `BC, CA, AB`. -/

/-- Non-vacuity: the hypotheses of `miquel_concyclic` are satisfied by a concrete triangle with
its side midpoints, so the theorem yields a genuine Miquel point there. -/
theorem miquel_example :
    ∃ O₁ O₂ O₃ M : ℂ,
      dist (⟨1 / 2, 3 / 2⟩ : ℂ) O₁ = dist (0 : ℂ) O₁ ∧ dist (2 : ℂ) O₁ = dist (0 : ℂ) O₁ ∧
      dist M O₁ = dist (0 : ℂ) O₁ ∧
      dist (2 : ℂ) O₂ = dist (4 : ℂ) O₂ ∧ dist (⟨5 / 2, 3 / 2⟩ : ℂ) O₂ = dist (4 : ℂ) O₂ ∧
      dist M O₂ = dist (4 : ℂ) O₂ ∧
      dist (⟨5 / 2, 3 / 2⟩ : ℂ) O₃ = dist (⟨1, 3⟩ : ℂ) O₃ ∧
      dist (⟨1 / 2, 3 / 2⟩ : ℂ) O₃ = dist (⟨1, 3⟩ : ℂ) O₃ ∧
      dist M O₃ = dist (⟨1, 3⟩ : ℂ) O₃ := by
  refine miquel_concyclic (n := 1 / 2) (t := 1 / 2) (u := 1 / 2) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · unfold Dp; norm_num
  · apply Complex.ext <;> norm_num
  · apply Complex.ext <;> norm_num
  · apply Complex.ext <;> norm_num
  all_goals norm_num

/-- Negative control: in the same configuration, the point `F = 2` lies on the circles `(AEF)`
and `(BFD)` but on no circle through `C, D, E` — membership of the third circle is a genuine
constraint, and the Miquel point is not just any point of the first two circles. -/
theorem miquel_negative_control :
    ¬ ∃ (O : ℂ) (r : ℝ), dist (⟨1, 3⟩ : ℂ) O = r ∧ dist (⟨5 / 2, 3 / 2⟩ : ℂ) O = r ∧
      dist (⟨1 / 2, 3 / 2⟩ : ℂ) O = r ∧ dist (2 : ℂ) O = r := by
  rintro ⟨O, r, h1, h2, h3, h4⟩
  have h := Q_eq_zero_of_dist h1 h2 h3 h4
  unfold Q at h
  norm_num at h

end Miquel
