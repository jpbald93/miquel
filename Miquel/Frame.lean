import Miquel.Coeffs

/-!
# Miquel's theorem — frame computation and circle lemmas

The Euclidean plane is modelled as `ℂ`. For a triangle `A B C` (not collinear) and points
`F = A + n (B - A)` on line `AB`, `E = A + t (C - A)` on line `CA`, `D = B + u (C - B)` on
line `BC` (with `D, E, F` different from the vertices), there is a point `M` lying on **every**
circle through `A, E, F`, on every circle through `B, F, D` and on every circle through
`C, D, E` (`miquel`). Since these three circles exist (`exists_circle`), this gives the
classical statement `miquel_concyclic`: the three circles `(AEF)`, `(BFD)`, `(CDE)` have a
common point.

Proof: in the frame of `Miquel.Coeffs`, `M` is the second intersection of the first two circles
(the radical-axis point `rpx, rpy`); the polynomial certificates `cert_x`, `cert_y`, `tang`
show that it lies on the third circle.
-/

noncomputable section

namespace Miquel

open Complex

/-- Minus twice the signed area of the triangle `a b c`; nonzero iff `a b c` are not collinear. -/
def Dp (a b c : ℂ) : ℝ :=
  -a.re * b.im + a.re * c.im + a.im * b.re - a.im * c.re - b.re * c.im + b.im * c.re

/-- `Dp` is (minus) the cross product of `b - a` and `c - a`. -/
lemma Dp_eq (a b c : ℂ) :
    Dp a b c = -((b.re - a.re) * (c.im - a.im) - (b.im - a.im) * (c.re - a.re)) := by
  unfold Dp; ring

/-- If `P R S` are not collinear and lie on the circle `(O, r)`, and `Q P R S M = 0`, then `M`
lies on that circle too. -/
lemma dist_eq_of_Q_eq_zero {P R S M O : ℂ} {r : ℝ} (hPRS : Dp P R S ≠ 0)
    (hP : dist P O = r) (hR : dist R O = r) (hS : dist S O = r) (hQ : Q P R S M = 0) :
    dist M O = r := by
  have gP := dist_sq_re_im P O
  have gR := dist_sq_re_im R O
  have gS := dist_sq_re_im S O
  rw [hP] at gP; rw [hR] at gR; rw [hS] at gS
  have hr : 0 ≤ r := by rw [← hP]; exact dist_nonneg
  have key : Dp P R S * ((M.re - O.re) ^ 2 + (M.im - O.im) ^ 2 - r ^ 2) = 0 := by
    unfold Q at hQ; unfold Dp
    linear_combination hQ +
      (R.re * S.im - R.re * M.im - R.im * S.re + R.im * M.re + S.re * M.im - S.im * M.re) * gP +
      (-P.re * S.im + P.re * M.im + P.im * S.re - P.im * M.re - S.re * M.im + S.im * M.re) * gR +
      (P.re * R.im - P.re * M.im - P.im * R.re + P.im * M.re + R.re * M.im - R.im * M.re) * gS
  have h2 : dist M O ^ 2 = r ^ 2 := by
    rw [dist_sq_re_im]
    have := (mul_eq_zero.mp key).resolve_left hPRS
    linarith
  exact (pow_left_inj₀ dist_nonneg hr two_ne_zero).1 h2

/-- `x`-coordinate (times `2 d`) of the circumcentre of `p, r, s`. -/
def circX (p0 p1 r0 r1 s0 s1 : ℝ) : ℝ :=
  -((r0 ^ 2 + r1 ^ 2 - (p0 ^ 2 + p1 ^ 2)) * (s1 - p1) -
    (s0 ^ 2 + s1 ^ 2 - (p0 ^ 2 + p1 ^ 2)) * (r1 - p1))

/-- `y`-coordinate (times `2 d`) of the circumcentre of `p, r, s`. -/
def circY (p0 p1 r0 r1 s0 s1 : ℝ) : ℝ :=
  -((r0 - p0) * (s0 ^ 2 + s1 ^ 2 - (p0 ^ 2 + p1 ^ 2)) -
    (s0 - p0) * (r0 ^ 2 + r1 ^ 2 - (p0 ^ 2 + p1 ^ 2)))

/-- Algebraic core of the circumcentre: `(ox, oy)` solving the perpendicular-bisector equations
is equidistant from `p`, `r`, `s`. -/
lemma circ_aux {p0 p1 r0 r1 s0 s1 ox oy d : ℝ}
    (hd : d = -p0 * r1 + p0 * s1 + p1 * r0 - p1 * s0 - r0 * s1 + r1 * s0) (hD : d ≠ 0)
    (hox : ox * (2 * d) = circX p0 p1 r0 r1 s0 s1)
    (hoy : oy * (2 * d) = circY p0 p1 r0 r1 s0 s1) :
    (r0 - ox) ^ 2 + (r1 - oy) ^ 2 = (p0 - ox) ^ 2 + (p1 - oy) ^ 2 ∧
      (s0 - ox) ^ 2 + (s1 - oy) ^ 2 = (p0 - ox) ^ 2 + (p1 - oy) ^ 2 := by
  unfold circX at hox; unfold circY at hoy
  subst hd
  constructor
  · apply mul_left_cancel₀ hD
    linear_combination (-(r0 - p0)) * hox + (-(r1 - p1)) * hoy
  · apply mul_left_cancel₀ hD
    linear_combination (-(s0 - p0)) * hox + (-(s1 - p1)) * hoy

/-- Three non-collinear points lie on a common circle. -/
lemma exists_circle {P R S : ℂ} (h : Dp P R S ≠ 0) :
    ∃ O : ℂ, dist R O = dist P O ∧ dist S O = dist P O := by
  have h2 : 2 * Dp P R S ≠ 0 := mul_ne_zero two_ne_zero h
  have hd : Dp P R S = -P.re * R.im + P.re * S.im + P.im * R.re - P.im * S.re - R.re * S.im +
      R.im * S.re := rfl
  obtain ⟨hr, hs⟩ := circ_aux (ox := circX P.re P.im R.re R.im S.re S.im / (2 * Dp P R S))
    (oy := circY P.re P.im R.re R.im S.re S.im / (2 * Dp P R S)) hd h
    (div_mul_cancel₀ _ h2) (div_mul_cancel₀ _ h2)
  refine ⟨⟨circX P.re P.im R.re R.im S.re S.im / (2 * Dp P R S),
    circY P.re P.im R.re R.im S.re S.im / (2 * Dp P R S)⟩, ?_, ?_⟩
  · rw [← pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero, dist_sq_re_im, dist_sq_re_im]
    exact hr
  · rw [← pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero, dist_sq_re_im, dist_sq_re_im]
    exact hs

/-! ### The radical-axis point of two circles through the origin -/

/-- Squared norm of the radical-axis normal of `a₁(x²+y²)+b₁x+c₁y` and `a₂(x²+y²)+b₂x+c₂y`. -/
def rpN (a1 b1 c1 a2 b2 c2 : ℝ) : ℝ := (a2 * b1 - a1 * b2) ^ 2 + (a2 * c1 - a1 * c2) ^ 2

/-- `x`-coordinate of the second intersection point of the two circles. -/
def rpx (a1 b1 c1 a2 b2 c2 : ℝ) : ℝ :=
  (b1 * c2 - c1 * b2) * (a2 * c1 - a1 * c2) / rpN a1 b1 c1 a2 b2 c2

/-- `y`-coordinate of the second intersection point of the two circles. -/
def rpy (a1 b1 c1 a2 b2 c2 : ℝ) : ℝ :=
  -((b1 * c2 - c1 * b2) * (a2 * b1 - a1 * b2)) / rpN a1 b1 c1 a2 b2 c2

/-- The radical-axis point lies on both circles. -/
lemma rp_on {a1 b1 c1 a2 b2 c2 : ℝ} (_hN : rpN a1 b1 c1 a2 b2 c2 ≠ 0) :
    a1 * (rpx a1 b1 c1 a2 b2 c2 ^ 2 + rpy a1 b1 c1 a2 b2 c2 ^ 2) +
        b1 * rpx a1 b1 c1 a2 b2 c2 + c1 * rpy a1 b1 c1 a2 b2 c2 = 0 ∧
      a2 * (rpx a1 b1 c1 a2 b2 c2 ^ 2 + rpy a1 b1 c1 a2 b2 c2 ^ 2) +
        b2 * rpx a1 b1 c1 a2 b2 c2 + c2 * rpy a1 b1 c1 a2 b2 c2 = 0 := by
  unfold rpx rpy
  unfold rpN at *
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- If the radical-axis point is the origin, the linear parts of the circles are parallel. -/
lemma rp_zero {a1 b1 c1 a2 b2 c2 : ℝ} (hN : rpN a1 b1 c1 a2 b2 c2 ≠ 0)
    (hx : rpx a1 b1 c1 a2 b2 c2 = 0) (hy : rpy a1 b1 c1 a2 b2 c2 = 0) :
    b1 * c2 - c1 * b2 = 0 := by
  unfold rpx at hx; unfold rpy at hy
  have hx' := (div_eq_zero_iff.mp hx).resolve_right hN
  have hy' := neg_eq_zero.mp ((div_eq_zero_iff.mp hy).resolve_right hN)
  have h : (b1 * c2 - c1 * b2) ^ 2 * rpN a1 b1 c1 a2 b2 c2 = 0 := by
    unfold rpN
    linear_combination ((b1 * c2 - c1 * b2) * (a2 * b1 - a1 * b2)) * hy' +
      ((b1 * c2 - c1 * b2) * (a2 * c1 - a1 * c2)) * hx'
  exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp h).resolve_right hN)

/-- Abstract core: given the certificate identities, the radical-axis point of the first two
circles lies on the third. -/
lemma core {a1 b1 c1 a2 b2 c2 a3 b3 c3 k3 K T : ℝ} (P1x P2x P1y P2y : ℝ → ℝ → ℝ)
    (hN : rpN a1 b1 c1 a2 b2 c2 ≠ 0) (hK : K ≠ 0)
    (hcx : ∀ x y : ℝ, K * x * (a3 * (x ^ 2 + y ^ 2) + b3 * x + c3 * y + k3) =
      P1x x y * (a1 * (x ^ 2 + y ^ 2) + b1 * x + c1 * y) +
        P2x x y * (a2 * (x ^ 2 + y ^ 2) + b2 * x + c2 * y))
    (hcy : ∀ x y : ℝ, K * y * (a3 * (x ^ 2 + y ^ 2) + b3 * x + c3 * y + k3) =
      P1y x y * (a1 * (x ^ 2 + y ^ 2) + b1 * x + c1 * y) +
        P2y x y * (a2 * (x ^ 2 + y ^ 2) + b2 * x + c2 * y))
    (htang : K * k3 = T * (b1 * c2 - c1 * b2)) :
    a3 * (rpx a1 b1 c1 a2 b2 c2 ^ 2 + rpy a1 b1 c1 a2 b2 c2 ^ 2) +
      b3 * rpx a1 b1 c1 a2 b2 c2 + c3 * rpy a1 b1 c1 a2 b2 c2 + k3 = 0 := by
  obtain ⟨h1, h2⟩ := rp_on hN
  have ex := hcx (rpx a1 b1 c1 a2 b2 c2) (rpy a1 b1 c1 a2 b2 c2)
  have ey := hcy (rpx a1 b1 c1 a2 b2 c2) (rpy a1 b1 c1 a2 b2 c2)
  rw [h1, h2, mul_zero, mul_zero, add_zero] at ex ey
  by_cases hxy : rpx a1 b1 c1 a2 b2 c2 = 0 ∧ rpy a1 b1 c1 a2 b2 c2 = 0
  · obtain ⟨hx0, hy0⟩ := hxy
    have hcr := rp_zero hN hx0 hy0
    have hk : K * k3 = 0 := by rw [htang, hcr, mul_zero]
    have hk3 : k3 = 0 := (mul_eq_zero.mp hk).resolve_left hK
    rw [hx0, hy0, hk3]; ring
  · rcases not_and_or.mp hxy with hx | hy
    · exact (mul_eq_zero.mp ex).resolve_left (mul_ne_zero hK hx)
    · exact (mul_eq_zero.mp ey).resolve_left (mul_ne_zero hK hy)

/-- Miquel's theorem in the frame of `Miquel.Coeffs`: the three circle polynomials have a
common zero. -/
lemma frame {w1 w2 c1 c2 n t u : ℝ} (hΔ : -c1 * w2 + c2 * w1 ≠ 0) (hn0 : n ≠ 0) (hn1 : n ≠ 1)
    (ht0 : t ≠ 0) (hu0 : u ≠ 0) :
    ∃ x y : ℝ, q1 w1 w2 c1 c2 n t u x y = 0 ∧ q2 w1 w2 c1 c2 n t u x y = 0 ∧
      q3 w1 w2 c1 c2 n t u x y = 0 := by
  have hW : w1 ^ 2 + w2 ^ 2 ≠ 0 := by
    intro h
    have e1 : w1 = 0 := by nlinarith [sq_nonneg w1, sq_nonneg w2]
    have e2 : w2 = 0 := by nlinarith [sq_nonneg w1, sq_nonneg w2]
    apply hΔ; rw [e1, e2]; ring
  have hn1' : n - 1 ≠ 0 := sub_ne_zero.mpr hn1
  have hK : KK w1 w2 c1 c2 n t u ≠ 0 := by
    unfold KK
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hn0 ht0) hu0) hn1') hW
  have hR : n ^ 2 * t * u * (n - 1) * (w1 ^ 2 + w2 ^ 2) * (-c1 * w2 + c2 * w1) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hn0) ht0)
      hu0) hn1') hW) (pow_ne_zero 2 hΔ)
  have hN : rpN (al1 w1 w2 c1 c2 n t u) (lx1 w1 w2 c1 c2 n t u) (ly1 w1 w2 c1 c2 n t u)
      (al2 w1 w2 c1 c2 n t u) (lx2 w1 w2 c1 c2 n t u) (ly2 w1 w2 c1 c2 n t u) ≠ 0 := by
    intro h0
    unfold rpN at h0
    apply hR
    rw [← sep w1 w2 c1 c2 n t u]
    have e1 : al2 w1 w2 c1 c2 n t u * lx1 w1 w2 c1 c2 n t u -
        al1 w1 w2 c1 c2 n t u * lx2 w1 w2 c1 c2 n t u = 0 := by
      nlinarith [sq_nonneg (al2 w1 w2 c1 c2 n t u * lx1 w1 w2 c1 c2 n t u -
        al1 w1 w2 c1 c2 n t u * lx2 w1 w2 c1 c2 n t u),
        sq_nonneg (al2 w1 w2 c1 c2 n t u * ly1 w1 w2 c1 c2 n t u -
        al1 w1 w2 c1 c2 n t u * ly2 w1 w2 c1 c2 n t u)]
    have e2 : al2 w1 w2 c1 c2 n t u * ly1 w1 w2 c1 c2 n t u -
        al1 w1 w2 c1 c2 n t u * ly2 w1 w2 c1 c2 n t u = 0 := by
      nlinarith [sq_nonneg (al2 w1 w2 c1 c2 n t u * lx1 w1 w2 c1 c2 n t u -
        al1 w1 w2 c1 c2 n t u * lx2 w1 w2 c1 c2 n t u),
        sq_nonneg (al2 w1 w2 c1 c2 n t u * ly1 w1 w2 c1 c2 n t u -
        al1 w1 w2 c1 c2 n t u * ly2 w1 w2 c1 c2 n t u)]
    rw [e1, e2]; ring
  obtain ⟨h1, h2⟩ := rp_on hN
  refine ⟨rpx (al1 w1 w2 c1 c2 n t u) (lx1 w1 w2 c1 c2 n t u) (ly1 w1 w2 c1 c2 n t u)
      (al2 w1 w2 c1 c2 n t u) (lx2 w1 w2 c1 c2 n t u) (ly2 w1 w2 c1 c2 n t u), rpy (al1 w1 w2 c1 c2 n t u) (lx1 w1 w2 c1 c2 n t u) (ly1 w1 w2 c1 c2 n t u)
      (al2 w1 w2 c1 c2 n t u) (lx2 w1 w2 c1 c2 n t u) (ly2 w1 w2 c1 c2 n t u), ?_, ?_, ?_⟩
  · unfold q1; exact h1
  · unfold q2; exact h2
  · unfold q3
    exact core (certx1 w1 w2 c1 c2 n t u) (certx2 w1 w2 c1 c2 n t u)
      (certy1 w1 w2 c1 c2 n t u) (certy2 w1 w2 c1 c2 n t u) hN hK
      (fun x y => by have := cert_x w1 w2 c1 c2 n t u x y; unfold q1 q2 q3 at this; exact this)
      (fun x y => by have := cert_y w1 w2 c1 c2 n t u x y; unfold q1 q2 q3 at this; exact this)
      (tang w1 w2 c1 c2 n t u)

end Miquel
