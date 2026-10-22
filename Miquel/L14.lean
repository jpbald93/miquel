import Miquel.Main
import Miquel.Bridge

/-!
# Layer 14: Mathlib-only restatement and witness

`l14_miquel` states Miquel's theorem in `ℂ` with Mathlib's `Collinear` for the non-degeneracy of
`ABC` and `line[ℝ, _, _]` membership (plus "not a vertex") for the points `D, E, F` on the
extended sides; `l14_miquel_cospherical` is the companion form with Mathlib's `Cospherical`.
Their types mention only Mathlib notions. `l14w_miquel` instantiates them at `A = 0`, `B = 2`,
`C = 2i`, `F = -2`, `E = -2i`, `D = 1 + i` (two points on extended sides), shows that the Miquel
point is forced to be `-2 - 2i`, distinct from all six points, and that the three circles are
pairwise distinct.
-/

open Complex

namespace Miquel

/-- A point of `line[ℝ, P, R]` has the form `P + s (R - P)`. -/
lemma l14_eq_of_mem_line {P R X : ℂ} (h : X ∈ line[ℝ, P, R]) :
    ∃ s : ℝ, X = P + (s : ℂ) * (R - P) := by
  obtain ⟨s, hs⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 h
  refine ⟨s, ?_⟩
  rw [← hs, AffineMap.lineMap_apply_module]
  simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-- **Miquel's theorem, Mathlib-only form.** Let `A B C` be non-collinear points of `ℂ`, and
`F, E, D` points of the lines `AB`, `AC`, `BC`, none of them a vertex. Then some point `M` lies on
every circle through `A, E, F`, every circle through `B, F, D` and every circle through
`C, D, E`. -/
theorem l14_miquel {A B C D E F : ℂ} (hABC : ¬ Collinear ℝ ({A, B, C} : Set ℂ))
    (hF : F ∈ line[ℝ, A, B]) (hE : E ∈ line[ℝ, A, C]) (hD : D ∈ line[ℝ, B, C])
    (hFA : F ≠ A) (hFB : F ≠ B) (hEA : E ≠ A) (hEC : E ≠ C) (hDB : D ≠ B) (hDC : D ≠ C) :
    ∃ M : ℂ,
      (∀ (O : ℂ) (r : ℝ), dist A O = r → dist E O = r → dist F O = r → dist M O = r) ∧
      (∀ (O : ℂ) (r : ℝ), dist B O = r → dist F O = r → dist D O = r → dist M O = r) ∧
      (∀ (O : ℂ) (r : ℝ), dist C O = r → dist D O = r → dist E O = r → dist M O = r) := by
  obtain ⟨n, rfl⟩ := l14_eq_of_mem_line hF
  obtain ⟨t, rfl⟩ := l14_eq_of_mem_line hE
  obtain ⟨u, rfl⟩ := l14_eq_of_mem_line hD
  have hDp : Dp A B C ≠ 0 := fun h => hABC ((Dp_eq_zero_iff_collinear A B C).1 h)
  have hAB : B - A ≠ 0 := by
    intro h; apply hABC; rw [sub_eq_zero.1 h]; simp [collinear_pair]
  have hAC : C - A ≠ 0 := by
    intro h; apply hABC; rw [sub_eq_zero.1 h]; simp [collinear_pair]
  have hBC : C - B ≠ 0 := by
    intro h; apply hABC; rw [sub_eq_zero.1 h]; simp [collinear_pair]
  refine miquel hDp rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
  · rintro rfl; simp at hFA
  · rintro rfl; apply hFB; simp
  · rintro rfl; simp at hEA
  · rintro rfl; apply hEC; simp
  · rintro rfl; simp at hDB
  · rintro rfl; apply hDC; simp

/-- **Miquel's theorem, Mathlib-only concyclic form**: under the same hypotheses there is `M` with
`{A, E, F, M}`, `{B, F, D, M}` and `{C, D, E, M}` each cospherical. -/
theorem l14_miquel_cospherical {A B C D E F : ℂ} (hABC : ¬ Collinear ℝ ({A, B, C} : Set ℂ))
    (hF : F ∈ line[ℝ, A, B]) (hE : E ∈ line[ℝ, A, C]) (hD : D ∈ line[ℝ, B, C])
    (hFA : F ≠ A) (hFB : F ≠ B) (hEA : E ≠ A) (hEC : E ≠ C) (hDB : D ≠ B) (hDC : D ≠ C) :
    ∃ M : ℂ, EuclideanGeometry.Cospherical ({A, E, F, M} : Set ℂ) ∧
      EuclideanGeometry.Cospherical ({B, F, D, M} : Set ℂ) ∧
      EuclideanGeometry.Cospherical ({C, D, E, M} : Set ℂ) := by
  obtain ⟨n, rfl⟩ := l14_eq_of_mem_line hF
  obtain ⟨t, rfl⟩ := l14_eq_of_mem_line hE
  obtain ⟨u, rfl⟩ := l14_eq_of_mem_line hD
  have hDp : Dp A B C ≠ 0 := fun h => hABC ((Dp_eq_zero_iff_collinear A B C).1 h)
  obtain ⟨O₁, O₂, O₃, M, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    miquel_concyclic hDp rfl rfl rfl (n := n) (t := t) (u := u)
      (by rintro rfl; simp at hFA) (by rintro rfl; apply hFB; simp)
      (by rintro rfl; simp at hEA) (by rintro rfl; apply hEC; simp)
      (by rintro rfl; simp at hDB) (by rintro rfl; apply hDC; simp)
  refine ⟨M, ⟨O₁, dist A O₁, ?_⟩, ⟨O₂, dist B O₂, ?_⟩, ⟨O₃, dist C O₃, ?_⟩⟩ <;>
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> first | rfl | assumption

/-- Two distances in `ℂ` agree when their squared coordinate expressions agree. -/
lemma l14_dist_eq {z w z' w' : ℂ}
    (h : (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 = (z'.re - w'.re) ^ 2 + (z'.im - w'.im) ^ 2) :
    dist z w = dist z' w' := by
  rw [Complex.dist_eq_re_im, Complex.dist_eq_re_im, h]

/-- Squared form of a distance in `ℂ`. -/
lemma l14_dist_sq (z w : ℂ) : dist z w ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
  rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity)]

/-- The witness triangle `0, 2, 2i` is not collinear. -/
lemma l14_ABC : ¬ Collinear ℝ ({(0 : ℂ), 2, 2 * I} : Set ℂ) := by
  rw [← Dp_eq_zero_iff_collinear]; unfold Dp; norm_num

/-- **Witness.** `A = 0`, `B = 2`, `C = 2i`, `F = -2 ∈ AB`, `E = -2i ∈ AC`, `D = 1 + i ∈ BC`
satisfy every hypothesis of `l14_miquel`; every point `M` given by its conclusion equals
`-2 - 2i`, which differs from `A, …, F`; the three circles have pairwise distinct centres
`-1 - i`, `-i`, `-1`, and the circles themselves differ (`B` is off the first, `C` off the
second, `A` off the third); and `l14_miquel_cospherical` applies. -/
theorem l14w_miquel :
    ¬ Collinear ℝ ({(0 : ℂ), 2, 2 * I} : Set ℂ) ∧
    (-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 2] ∧ (-2 * I : ℂ) ∈ line[ℝ, (0 : ℂ), 2 * I] ∧
    (1 + I : ℂ) ∈ line[ℝ, (2 : ℂ), 2 * I] ∧
    (-2 : ℂ) ≠ 0 ∧ (-2 : ℂ) ≠ 2 ∧ (-2 * I : ℂ) ≠ 0 ∧ (-2 * I : ℂ) ≠ 2 * I ∧
    (1 + I : ℂ) ≠ 2 ∧ (1 + I : ℂ) ≠ 2 * I ∧
    (∀ M : ℂ,
      ((∀ (O : ℂ) (r : ℝ), dist 0 O = r → dist (-2 * I) O = r → dist (-2) O = r →
          dist M O = r) ∧
        (∀ (O : ℂ) (r : ℝ), dist 2 O = r → dist (-2) O = r → dist (1 + I) O = r →
          dist M O = r) ∧
        (∀ (O : ℂ) (r : ℝ), dist (2 * I) O = r → dist (1 + I) O = r → dist (-2 * I) O = r →
          dist M O = r)) →
      M = -2 - 2 * I ∧ M ≠ 0 ∧ M ≠ 2 ∧ M ≠ 2 * I ∧ M ≠ 1 + I ∧ M ≠ -2 * I ∧ M ≠ -2) ∧
    (∃ M : ℂ,
      (∀ (O : ℂ) (r : ℝ), dist 0 O = r → dist (-2 * I) O = r → dist (-2) O = r →
          dist M O = r) ∧
        (∀ (O : ℂ) (r : ℝ), dist 2 O = r → dist (-2) O = r → dist (1 + I) O = r →
          dist M O = r) ∧
        (∀ (O : ℂ) (r : ℝ), dist (2 * I) O = r → dist (1 + I) O = r → dist (-2 * I) O = r →
          dist M O = r)) ∧
    (-1 - I : ℂ) ≠ -I ∧ (-1 - I : ℂ) ≠ -1 ∧ (-I : ℂ) ≠ -1 ∧
    dist (2 : ℂ) (-1 - I) ≠ dist (0 : ℂ) (-1 - I) ∧ dist (2 * I) (-I) ≠ dist (2 : ℂ) (-I) ∧
    dist (0 : ℂ) (-1) ≠ dist (2 * I) (-1) ∧
    (∃ M : ℂ, EuclideanGeometry.Cospherical ({(0 : ℂ), -2 * I, -2, M} : Set ℂ) ∧
      EuclideanGeometry.Cospherical ({(2 : ℂ), -2, 1 + I, M} : Set ℂ) ∧
      EuclideanGeometry.Cospherical ({2 * I, 1 + I, -2 * I, M} : Set ℂ)) := by
  have hF : (-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 2] :=
    (mem_affineSpan_pair_iff_exists_lineMap_eq).2
      ⟨-1, by rw [AffineMap.lineMap_apply_module]; apply Complex.ext <;> simp⟩
  have hE : (-2 * I : ℂ) ∈ line[ℝ, (0 : ℂ), 2 * I] :=
    (mem_affineSpan_pair_iff_exists_lineMap_eq).2
      ⟨-1, by rw [AffineMap.lineMap_apply_module]; apply Complex.ext <;> simp⟩
  have hD : (1 + I : ℂ) ∈ line[ℝ, (2 : ℂ), 2 * I] :=
    (mem_affineSpan_pair_iff_exists_lineMap_eq).2
      ⟨1 / 2, by rw [AffineMap.lineMap_apply_module]; apply Complex.ext <;> norm_num⟩
  have ne : ∀ z w : ℂ, (z.re ≠ w.re ∨ z.im ≠ w.im) → z ≠ w := by
    rintro z w h rfl; tauto
  have dne : ∀ {a b c d : ℂ}, (a.re - b.re) ^ 2 + (a.im - b.im) ^ 2 ≠
      (c.re - d.re) ^ 2 + (c.im - d.im) ^ 2 → dist a b ≠ dist c d := by
    intro a b c d h he
    apply h
    rw [← l14_dist_sq, ← l14_dist_sq, he]
  have h1 : (-2 : ℂ) ≠ 0 := ne _ _ (by norm_num)
  have h2 : (-2 : ℂ) ≠ 2 := ne _ _ (by norm_num)
  have h3 : (-2 * I : ℂ) ≠ 0 := ne _ _ (by norm_num)
  have h4 : (-2 * I : ℂ) ≠ 2 * I := ne _ _ (by norm_num)
  have h5 : (1 + I : ℂ) ≠ 2 := ne _ _ (by norm_num)
  have h6 : (1 + I : ℂ) ≠ 2 * I := ne _ _ (by norm_num)
  refine ⟨l14_ABC, hF, hE, hD, h1, h2, h3, h4, h5, h6, ?_,
    l14_miquel l14_ABC hF hE hD h1 h2 h3 h4 h5 h6, ne _ _ (by norm_num),
      ne _ _ (by norm_num), ne _ _ (by norm_num), dne (by norm_num), dne (by norm_num),
      dne (by norm_num), l14_miquel_cospherical l14_ABC hF hE hD h1 h2 h3 h4 h5 h6⟩
  rintro M ⟨c1, c2, c3⟩
  have e1 := c1 (-1 - I) _ rfl (l14_dist_eq (by norm_num)) (l14_dist_eq (by norm_num))
  have e2 := c2 (-I) _ rfl (l14_dist_eq (by norm_num)) (l14_dist_eq (by norm_num))
  have e3 := c3 (-1) _ rfl (l14_dist_eq (by norm_num)) (l14_dist_eq (by norm_num))
  have s1 := congrArg (· ^ 2) e1
  have s2 := congrArg (· ^ 2) e2
  have s3 := congrArg (· ^ 2) e3
  simp only [l14_dist_sq] at s1 s2 s3
  norm_num at s1 s2 s3
  have hx : M.re = -2 := by nlinarith
  have hy : M.im = -2 := by nlinarith
  have hM : M = -2 - 2 * I := Complex.ext (by simp [hx]) (by simp [hy])
  subst hM
  exact ⟨rfl, ne _ _ (by norm_num), ne _ _ (by norm_num), ne _ _ (by norm_num),
    ne _ _ (by norm_num), ne _ _ (by norm_num), ne _ _ (by norm_num)⟩

end Miquel
