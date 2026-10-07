import Miquel.Basic

/-!
# Miquel's theorem — coordinate coefficients and the algebraic certificate

Frame (translation-invariant): `A` arbitrary, `B = A + w`, `C = A + c`, `F = A + n w`,
`E = A + t c`, `D = B + u (c - w)`, and a test point `M = F + (x, y)`.
In this frame `Q A E F M = q1`, `Q B F D M = q2`, `Q C D E M = q3`, where
`qᵢ = alᵢ (x² + y²) + lxᵢ x + lyᵢ y (+ kk3 for i = 3)` (the first two circles pass through
`F`, so have no constant term). The certificate lemmas `cert_x`, `cert_y` express
`K x q3` and `K y q3` as combinations of `q1`, `q2` (with polynomial multipliers), where
`K = n t u (n - 1) |w|²`. All identities were generated with SymPy and are checked here by `ring`.
-/

noncomputable section

namespace Miquel

/-- coefficient `al1` of `q1`. -/
def al1 (w1 w2 c1 c2 n t _u : ℝ) : ℝ :=
  n*t*(-c1*w2 + c2*w1)

/-- coefficient `lx1` of `q1`. -/
def lx1 (w1 w2 c1 c2 n t _u : ℝ) : ℝ :=
  n*t*(c1^2*t*w2 - 2*c1*n*w1*w2 + c2^2*t*w2 + c2*n*w1^2 - c2*n*w2^2)

/-- coefficient `ly1` of `q1`. -/
def ly1 (w1 w2 c1 c2 n t _u : ℝ) : ℝ :=
  -n*t*(c1^2*t*w1 - c1*n*w1^2 + c1*n*w2^2 + c2^2*t*w1 - 2*c2*n*w1*w2)

/-- coefficient `al2` of `q2`. -/
def al2 (w1 w2 c1 c2 n _t u : ℝ) : ℝ :=
  -u*(n - 1)*(-c1*w2 + c2*w1)

/-- coefficient `lx2` of `q2`. -/
def lx2 (w1 w2 c1 c2 n _t u : ℝ) : ℝ :=
  -u*(n - 1)*(c1^2*u*w2 - 2*c1*n*w1*w2 - 2*c1*u*w1*w2 + 2*c1*w1*w2 + c2^2*u*w2 + c2*n*w1^2 - c2*n*w2^2 - 2*c2*u*w2^2 - c2*w1^2 + c2*w2^2 + n*w1^2*w2 + n*w2^3 + u*w1^2*w2 + u*w2^3 - w1^2*w2 - w2^3)

/-- coefficient `ly2` of `q2`. -/
def ly2 (w1 w2 c1 c2 n _t u : ℝ) : ℝ :=
  u*(n - 1)*(c1^2*u*w1 - c1*n*w1^2 + c1*n*w2^2 - 2*c1*u*w1^2 + c1*w1^2 - c1*w2^2 + c2^2*u*w1 - 2*c2*n*w1*w2 - 2*c2*u*w1*w2 + 2*c2*w1*w2 + n*w1^3 + n*w1*w2^2 + u*w1^3 + u*w1*w2^2 - w1^3 - w1*w2^2)

/-- coefficient `al3` of `q3`. -/
def al3 (w1 w2 c1 c2 _n t u : ℝ) : ℝ :=
  (t - 1)*(u - 1)*(-c1*w2 + c2*w1)

/-- coefficient `lx3` of `q3`. -/
def lx3 (w1 w2 c1 c2 n t u : ℝ) : ℝ :=
  (t - 1)*(u - 1)*(-c1^2*c2*t + c1^2*c2*u + c1^2*t*w2 + c1^2*w2 - 2*c1*c2*u*w1 - 2*c1*n*w1*w2 - c2^3*t + c2^3*u + c2^2*t*w2 - 2*c2^2*u*w2 + c2^2*w2 + 2*c2*n*w1^2 + c2*u*w1^2 + c2*u*w2^2 - c2*w1^2 - c2*w2^2)

/-- coefficient `ly3` of `q3`. -/
def ly3 (w1 w2 c1 c2 n t u : ℝ) : ℝ :=
  -(t - 1)*(u - 1)*(-c1^3*t + c1^3*u + c1^2*t*w1 - 2*c1^2*u*w1 + c1^2*w1 - c1*c2^2*t + c1*c2^2*u - 2*c1*c2*u*w2 + 2*c1*n*w2^2 + c1*u*w1^2 + c1*u*w2^2 - c1*w1^2 - c1*w2^2 + c2^2*t*w1 + c2^2*w1 - 2*c2*n*w1*w2)

/-- constant term of `q3`. -/
def kk3 (w1 w2 c1 c2 n t u : ℝ) : ℝ :=
  -(t - 1)*(u - 1)*(-c1*w2 + c2*w1)*(c1^2*n*t - c1^2*n*u - c1^2*t + 2*c1*n*u*w1 + c2^2*n*t - c2^2*n*u - c2^2*t + 2*c2*n*u*w2 - n^2*w1^2 - n^2*w2^2 - n*u*w1^2 - n*u*w2^2 + n*w1^2 + n*w2^2)

/-- certificate multiplier `certx1`. -/
def certx1 (w1 w2 c1 c2 n t u : ℝ) (x y : ℝ) : ℝ :=
  u*(n - 1)*(t - 1)*(u - 1)*(c1^2*u*w1 - c1*n*w1^2 + c1*n*w2^2 - 2*c1*u*w1^2 + c1*w1^2 - c1*w1*x - c1*w2^2 + c1*w2*y + c2^2*u*w1 - 2*c2*n*w1*w2 - 2*c2*u*w1*w2 + 2*c2*w1*w2 - c2*w1*y - c2*w2*x + n*w1^3 + n*w1*w2^2 + u*w1^3 + u*w1*w2^2 - w1^3 + w1^2*x - w1*w2^2 + w2^2*x)

/-- certificate multiplier `certx2`. -/
def certx2 (w1 w2 c1 c2 n t u : ℝ) (x y : ℝ) : ℝ :=
  -n*t*(t - 1)*(u - 1)*(-c1^2*t*w1 + c1*n*w1^2 - c1*n*w2^2 + c1*w1*x - c1*w2*y - c2^2*t*w1 + 2*c2*n*w1*w2 + c2*w1*y + c2*w2*x)

/-- certificate multiplier `certy1`. -/
def certy1 (w1 w2 c1 c2 n t u : ℝ) (x y : ℝ) : ℝ :=
  u*(n - 1)*(t - 1)*(u - 1)*(c1^2*u*w2 - 2*c1*n*w1*w2 - 2*c1*u*w1*w2 + 2*c1*w1*w2 - c1*w1*y - c1*w2*x + c2^2*u*w2 + c2*n*w1^2 - c2*n*w2^2 - 2*c2*u*w2^2 - c2*w1^2 + c2*w1*x + c2*w2^2 - c2*w2*y + n*w1^2*w2 + n*w2^3 + u*w1^2*w2 + u*w2^3 - w1^2*w2 + w1^2*y - w2^3 + w2^2*y)

/-- certificate multiplier `certy2`. -/
def certy2 (w1 w2 c1 c2 n t u : ℝ) (x y : ℝ) : ℝ :=
  n*t*(t - 1)*(u - 1)*(c1^2*t*w2 - 2*c1*n*w1*w2 - c1*w1*y - c1*w2*x + c2^2*t*w2 + c2*n*w1^2 - c2*n*w2^2 + c2*w1*x - c2*w2*y)

/-- The circle polynomial of `(AEF)` in the frame. -/
def q1 (w1 w2 c1 c2 n t u x y : ℝ) : ℝ :=
  al1 w1 w2 c1 c2 n t u * (x ^ 2 + y ^ 2) + lx1 w1 w2 c1 c2 n t u * x + ly1 w1 w2 c1 c2 n t u * y

/-- The circle polynomial of `(BFD)` in the frame. -/
def q2 (w1 w2 c1 c2 n t u x y : ℝ) : ℝ :=
  al2 w1 w2 c1 c2 n t u * (x ^ 2 + y ^ 2) + lx2 w1 w2 c1 c2 n t u * x + ly2 w1 w2 c1 c2 n t u * y

/-- The circle polynomial of `(CDE)` in the frame. -/
def q3 (w1 w2 c1 c2 n t u x y : ℝ) : ℝ :=
  al3 w1 w2 c1 c2 n t u * (x ^ 2 + y ^ 2) + lx3 w1 w2 c1 c2 n t u * x + ly3 w1 w2 c1 c2 n t u * y + kk3 w1 w2 c1 c2 n t u

/-- The scalar `K = n t u (n - 1) |w|²`. -/
def KK (w1 w2 _c1 _c2 n t u : ℝ) : ℝ := n * t * u * (n - 1) * (w1 ^ 2 + w2 ^ 2)

/-- Certificate, `x`-part: `K x q3 = P₁ q1 + P₂ q2`. -/
lemma cert_x (w1 w2 c1 c2 n t u x y : ℝ) :
    KK w1 w2 c1 c2 n t u * x * q3 w1 w2 c1 c2 n t u x y =
      certx1 w1 w2 c1 c2 n t u x y * q1 w1 w2 c1 c2 n t u x y + certx2 w1 w2 c1 c2 n t u x y * q2 w1 w2 c1 c2 n t u x y := by
  unfold KK q1 q2 q3 certx1 certx2 al1 lx1 ly1 al2 lx2 ly2 al3 lx3 ly3 kk3
  ring

/-- Certificate, `y`-part: `K y q3 = P₁ q1 + P₂ q2`. -/
lemma cert_y (w1 w2 c1 c2 n t u x y : ℝ) :
    KK w1 w2 c1 c2 n t u * y * q3 w1 w2 c1 c2 n t u x y =
      certy1 w1 w2 c1 c2 n t u x y * q1 w1 w2 c1 c2 n t u x y + certy2 w1 w2 c1 c2 n t u x y * q2 w1 w2 c1 c2 n t u x y := by
  unfold KK q1 q2 q3 certy1 certy2 al1 lx1 ly1 al2 lx2 ly2 al3 lx3 ly3 kk3
  ring

/-- Tangency identity: the constant term of `q3` is a multiple of the cross product of the
linear parts of `q1`, `q2`. -/
lemma tang (w1 w2 c1 c2 n t u : ℝ) :
    KK w1 w2 c1 c2 n t u * kk3 w1 w2 c1 c2 n t u =
      (t - 1) * (u - 1) * (lx1 w1 w2 c1 c2 n t u * ly2 w1 w2 c1 c2 n t u - ly1 w1 w2 c1 c2 n t u * lx2 w1 w2 c1 c2 n t u) := by
  unfold KK kk3 lx1 ly1 lx2 ly2
  ring

/-- Separation identity: the radical-axis normal is nonzero in the non-degenerate case. -/
lemma sep (w1 w2 c1 c2 n t u : ℝ) :
    (al2 w1 w2 c1 c2 n t u * lx1 w1 w2 c1 c2 n t u - al1 w1 w2 c1 c2 n t u * lx2 w1 w2 c1 c2 n t u) * (-n * w1) +
      (al2 w1 w2 c1 c2 n t u * ly1 w1 w2 c1 c2 n t u - al1 w1 w2 c1 c2 n t u * ly2 w1 w2 c1 c2 n t u) * (-n * w2) =
      n ^ 2 * t * u * (n - 1) * (w1 ^ 2 + w2 ^ 2) * (-c1 * w2 + c2 * w1) ^ 2 := by
  unfold al1 lx1 ly1 al2 lx2 ly2
  ring

end Miquel
