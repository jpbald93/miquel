import Miquel.Basic
import Miquel.Coeffs
import Miquel.Frame
import Miquel.Main
import Miquel.Witness
import Miquel.Bridge
import Miquel.L14

/-!
# Layer 15: independent classical statements

Layer 15. These definitions and statements were written independently, from textbook statements,
by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves
(or proves part of) one of them from this development.
-/

open EuclideanGeometry

noncomputable section

namespace Miquel.Classical

abbrev E2 := EuclideanSpace ℝ (Fin 2)

def classical_B2_a : Prop := ∀ (A B C D E F : E2) (h : AffineIndependent ℝ ![A, B, C])
    (hD : Sbtw ℝ B D C) (hE : Sbtw ℝ C E A) (hF : Sbtw ℝ A F B),
    ∃ M : E2, Cospherical ({A, E, F, M} : Set E2) ∧ Cospherical ({B, F, D, M} : Set E2) ∧
      Cospherical ({C, D, E, M} : Set E2)

def classical_B2_b : Prop := ∀ (A B C D E F : E2) (h : AffineIndependent ℝ ![A, B, C])
    (hD : D ∈ line[ℝ, B, C]) (hE : E ∈ line[ℝ, C, A]) (hF : F ∈ line[ℝ, A, B])
    (hDB : D ≠ B) (hDC : D ≠ C) (hEC : E ≠ C) (hEA : E ≠ A) (hFA : F ≠ A) (hFB : F ≠ B),
    ∃ M : E2, Cospherical ({A, E, F, M} : Set E2) ∧ Cospherical ({B, F, D, M} : Set E2) ∧
      Cospherical ({C, D, E, M} : Set E2)

def classical_B2_obligation : Prop := ∀ (A B C D E F : E2) (h : AffineIndependent ℝ ![A, B, C])
    (hD : D ∈ line[ℝ, B, C]) (hE : E ∈ line[ℝ, C, A]) (hF : F ∈ line[ℝ, A, B])
    (hDB : D ≠ B) (hDC : D ≠ C) (hEC : E ≠ C) (hEA : E ≠ A) (hFA : F ≠ A) (hFB : F ≠ B),
    ¬ Collinear ℝ ({A, E, F} : Set E2) ∧ ¬ Collinear ℝ ({B, F, D} : Set E2) ∧
      ¬ Collinear ℝ ({C, D, E} : Set E2)

/-! ### Transport -/

/-- the isometry `E2 ≃ ℂ` -/
abbrev φ : E2 ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm

lemma l15_line {P Q X : E2} (h : X ∈ line[ℝ, P, Q]) :
    ∃ s : ℝ, φ X = φ P + (s : ℂ) * (φ Q - φ P) := by
  obtain ⟨s, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 h
  refine ⟨s, ?_⟩
  rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, Complex.real_smul]
  ring

lemma l15_param_ne {P Q X : E2} {s : ℝ} (hs : φ X = φ P + (s : ℂ) * (φ Q - φ P))
    (h0 : X ≠ P) (h1 : X ≠ Q) : s ≠ 0 ∧ s ≠ 1 := by
  refine ⟨fun h => h0 (φ.injective (by rw [hs, h]; simp)),
    fun h => h1 (φ.injective (by rw [hs, h]; simp))⟩

lemma l15_ai_iff (P R S : E2) :
    AffineIndependent ℝ ![φ P, φ R, φ S] ↔ AffineIndependent ℝ ![P, R, S] := by
  have e : ![φ P, φ R, φ S] = (φ.toLinearEquiv.toAffineEquiv : E2 → ℂ) ∘ ![P, R, S] := by
    funext i; fin_cases i <;> rfl
  rw [e, AffineEquiv.affineIndependent_iff]

lemma l15_Dp_ne_iff (P R S : E2) :
    Miquel.Dp (φ P) (φ R) (φ S) ≠ 0 ↔ ¬ Collinear ℝ ({P, R, S} : Set E2) := by
  rw [ne_eq, Miquel.Dp_eq_zero_iff_collinear, ← affineIndependent_iff_not_collinear_set,
    ← affineIndependent_iff_not_collinear_set, l15_ai_iff]

lemma l15_Dp_ne {A B C : E2} (h : AffineIndependent ℝ ![A, B, C]) :
    Miquel.Dp (φ A) (φ B) (φ C) ≠ 0 :=
  (l15_Dp_ne_iff A B C).2 (affineIndependent_iff_not_collinear_set.1 h)

lemma l15_cosph {P R S M : E2} {O : ℂ} (hR : dist (φ R) O = dist (φ P) O)
    (hS : dist (φ S) O = dist (φ P) O) (hM : dist (φ M) O = dist (φ P) O) :
    Cospherical ({P, R, S, M} : Set E2) := by
  refine ⟨φ.symm O, dist (φ P) O, ?_⟩
  have key : ∀ X : E2, dist X (φ.symm O) = dist (φ X) O := fun X => by
    rw [← φ.dist_map X (φ.symm O), LinearIsometryEquiv.apply_symm_apply]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro X (rfl | rfl | rfl | rfl) <;> rw [key] <;> assumption

/-! ### B2(b) covered -/

theorem cov_B2_b : classical_B2_b := by
  intro A B C D E F h hD hE hF hDB hDC hEC hEA hFA hFB
  obtain ⟨n, hn⟩ := l15_line hF
  obtain ⟨t, ht⟩ := l15_line (show E ∈ line[ℝ, A, C] by rwa [Set.pair_comm])
  obtain ⟨u, hu⟩ := l15_line hD
  obtain ⟨hn0, hn1⟩ := l15_param_ne hn hFA hFB
  obtain ⟨ht0, ht1⟩ := l15_param_ne ht hEA hEC
  obtain ⟨hu0, hu1⟩ := l15_param_ne hu hDB hDC
  obtain ⟨O₁, O₂, O₃, M, h1E, h1F, h1M, h2F, h2D, h2M, h3D, h3E, h3M⟩ :=
    Miquel.miquel_concyclic (l15_Dp_ne h) hn ht hu hn0 hn1 ht0 ht1 hu0 hu1
  refine ⟨φ.symm M, ?_, ?_, ?_⟩
  · exact l15_cosph h1E h1F (by rwa [LinearIsometryEquiv.apply_symm_apply])
  · exact l15_cosph h2F h2D (by rwa [LinearIsometryEquiv.apply_symm_apply])
  · exact l15_cosph h3D h3E (by rwa [LinearIsometryEquiv.apply_symm_apply])

/-! ### B2(a) covered (open sides ⊆ side lines minus vertices) -/

theorem cov_B2_a : classical_B2_a := by
  intro A B C D E F h hD hE hF
  exact cov_B2_b A B C D E F h hD.wbtw.mem_affineSpan hE.wbtw.mem_affineSpan
    hF.wbtw.mem_affineSpan hD.ne_left hD.ne_right hE.ne_left hE.ne_right hF.ne_left hF.ne_right

/-! ### B2 obligation (NEW PROOF, same frame bridge as the repository's `miquel_concyclic`) -/

lemma l15_not_collinear {P R S : E2} (hd : Miquel.Dp (φ P) (φ R) (φ S) ≠ 0) :
    ¬ Collinear ℝ ({P, R, S} : Set E2) := (l15_Dp_ne_iff P R S).1 hd

theorem cov_B2_obligation : classical_B2_obligation := by
  intro A B C D E F h hD hE hF hDB hDC hEC hEA hFA hFB
  obtain ⟨n, hn⟩ := l15_line hF
  obtain ⟨t, ht⟩ := l15_line (show E ∈ line[ℝ, A, C] by rwa [Set.pair_comm])
  obtain ⟨u, hu⟩ := l15_line hD
  obtain ⟨hn0, hn1⟩ := l15_param_ne hn hFA hFB
  obtain ⟨ht0, ht1⟩ := l15_param_ne ht hEA hEC
  obtain ⟨hu0, hu1⟩ := l15_param_ne hu hDB hDC
  have hΔ := l15_Dp_ne h
  set a := φ A; set b := φ B; set c := φ C; set d := φ D; set e := φ E; set f := φ F
  obtain ⟨-, -, -, d1, d2, d3, d0⟩ := Miquel.bridge (a1 := a.re) (a2 := a.im)
    (w1 := b.re - a.re) (w2 := b.im - a.im) (c1 := c.re - a.re) (c2 := c.im - a.im)
    (x := 0) (y := 0) (n := n) (t := t) (u := u) (A := a) (B := b) (C := c) (D := d) (E := e)
    (F := f) (M := f) rfl rfl (by ring) (by ring)
    (by ring) (by ring) (by rw [hn, Miquel.line_re]) (by rw [hn, Miquel.line_im])
    (by rw [ht, Miquel.line_re]) (by rw [ht, Miquel.line_im]) (by rw [hu, Miquel.line_re]; ring)
    (by rw [hu, Miquel.line_im]; ring) (by rw [hn, Miquel.line_re]; ring)
    (by rw [hn, Miquel.line_im]; ring)
  have hΔ' : -(c.re - a.re) * (b.im - a.im) + (c.im - a.im) * (b.re - a.re) ≠ 0 := by
    intro h0; apply hΔ; rw [d0, h0, neg_zero]
  refine ⟨l15_not_collinear ?_, l15_not_collinear ?_, l15_not_collinear ?_⟩
  · rw [d1]; unfold Miquel.al1; exact mul_ne_zero (mul_ne_zero hn0 ht0) hΔ'
  · rw [d2]; unfold Miquel.al2
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hu0) (sub_ne_zero.mpr hn1)) hΔ'
  · rw [d3]; unfold Miquel.al3
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr ht1) (sub_ne_zero.mpr hu1)) hΔ'

end Miquel.Classical
