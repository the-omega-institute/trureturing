/- GID: D5/S3/Combinatorics/SpectralGraph/PairTailSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/PairTailSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict bounded-root windows and actual ideal-graph tail candidates. -/
import D5.S3.Combinatorics.SpectralGraph.PairTailArithmetic
import D5.S3.Combinatorics.SpectralGraph.PairGapSigns
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionLift

/-! Sources: four-prime-large-tail, four-prime-tail-reduction,
four-prime-harmonic-tail and four-prime-unique-tail, supplied PR9
revision 6d491f77b35dec808fc777b69939c56cdae5dc02. All positive
natural a,b,c are retained, without ordering a and b. The stronger
harmonic window assumes b<c; equality is the separate double-pair
family. A root of a candidate quadratic is only a necessary test for
the actual graph and does not imply integral spectrum. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix Finset
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.PairTailSpectrum
open PairedIdealIntersectionObstructions PairedIdealIntersectionDeterminants
open IdealIntersectionSupport IdealIntersectionObstructions PairedIdealIntersectionLift

private theorem between (a b c l u : ℝ) (hlu : l<u)
    (hl : (tensorK a b c-l • 1).det<0)
    (hu : 0<(tensorK a b c-u • 1).det) :
    ∃ e : ℝ, l<e ∧ e<u ∧ ∃ h : Fin 2 × Fin 2 → ℝ,
      h≠0 ∧ tensorK a b c*ᵥh=e • h := by
  let f:=fun x : ℝ => (tensorK a b c-x • 1).det
  have hf : Continuous f := by dsimp [f]; fun_prop
  obtain ⟨e,he,hfe⟩:=intermediate_value_Icc hlu.le hf.continuousOn
    (show (0:ℝ)∈Set.Icc (f l) (f u) from ⟨hl.le,hu.le⟩)
  have hel : l<e := by
    have hn : l≠e := by intro h; rw [←h] at hfe; exact hl.ne hfe
    exact lt_of_le_of_ne he.1 hn
  have heu : e<u := by
    have hn : e≠u := by intro h; rw [h] at hfe; exact hu.ne' hfe
    exact lt_of_le_of_ne he.2 hn
  obtain ⟨h,hh,hZ⟩:=Matrix.exists_mulVec_eq_zero_iff.mpr hfe
  rw [sub_mulVec,smul_mulVec,one_mulVec] at hZ
  exact ⟨e,hel,heu,h,hh,sub_eq_zero.mp hZ⟩

/-- The exact strict upper endpoint of the bounded-root interval. -/
theorem upper_endpoint (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hc : 1≤c) :
    0<(tensorK a b c-((a+1)*(b+1)) • 1).det := by
  have hid : (tensorK a b c-((a+1)*(b+1)) • 1).det=
      a^2*b*c*((c-1)*((a+1)^2*b^2+(2*a^2+2*a+1)*b+(a+1)^2)+
        ((a*b-1/2)^2+3/4+2*a*b^2+b^2+a^2+2*a)) := by
    rw [det_tensorK_sub_scalar]
    ring
  rw [hid]
  have hc0 : 0<c := by linarith
  have hcm : 0≤c-1 := by linarith
  positivity

/-- A genuine eigenpair in the full strict interval, for every positive
integer-sized tail. No compression is used as an eigenvalue proxy. -/
theorem bounded_eigenpair (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hc : 1≤c) :
    ∃ e : ℝ, a+1<e ∧ e<(a+1)*(b+1) ∧
      ∃ h : Fin 2 × Fin 2 → ℝ, h≠0 ∧ tensorK a b c*ᵥh=e • h := by
  apply between a b c _ _ (by nlinarith)
  · have he : (tensorK a b c-(a+1) • 1).det= -a^2*b^2*c^2*(2*a+1) := by
      rw [det_tensorK_sub_scalar]
      ring
    rw [he]
    have hc0 : 0<c := by linarith
    have hp : 0<a^2*b^2*c^2*(2*a+1) := by positivity
    linarith
  · exact upper_endpoint a b c ha hb hc

private def harmonicBracket (a b c : ℝ) : ℝ :=
  2*a^3*b^3+6*a^3*b^2*c+6*a^3*b*c^2+2*a^3*c^3+
  a^2*b^3*c+2*a^2*b^3+2*a^2*b^2*c^2+6*a^2*b^2*c+
  a^2*b*c^3+6*a^2*b*c^2+2*a^2*c^3+
  2*a*b^3*c^2+2*a*b^3*c+2*a*b^2*c^3+4*a*b^2*c^2+
  2*a*b^2*c+2*a*b*c^3+2*a*b*c^2+
  2*b^3*c^2+2*b^3*c+2*b^2*c^3+2*b*c^3

/-- The exact harmonic endpoint is strictly positive on unequal tails. -/
theorem harmonic_endpoint (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hbc : b<c) :
    0<(tensorK a b c-(a+1+2*b*c/(b+c)) • 1).det := by
  have hc : 0<c := by linarith
  have hs : b+c≠0 := by positivity
  have hid : (tensorK a b c-(a+1+2*b*c/(b+c)) • 1).det=
      b*c*(b-c)^2*harmonicBracket a b c/(b+c)^4 := by
    rw [det_tensorK_sub_scalar]
    dsimp [harmonicBracket]
    field_simp
    <;> ring
  have hp : 0<harmonicBracket a b c := by unfold harmonicBracket; positivity
  rw [hid]
  have hn : b-c≠0 := by linarith
  positivity

/-- The full harmonic interval for an actual nonzero tensor eigenpair. -/
theorem harmonic_eigenpair (a b c : ℝ) (ha : 0<a) (hb : 1≤b) (hbc : b<c) :
    ∃ e : ℝ, a+b+1<e ∧ e<a+1+2*b*c/(b+c) ∧ e<a+2*b+1 ∧
      ∃ h : Fin 2 × Fin 2 → ℝ, h≠0 ∧ tensorK a b c*ᵥh=e • h := by
  have hb0 : 0<b := by linarith
  have hs : 0<b+c := by linarith
  have hl : a+b+1<a+1+2*b*c/(b+c) := by
    have hp : b<2*b*c/(b+c) := (lt_div_iff₀ hs).mpr (by nlinarith)
    linarith
  obtain ⟨e,hel,heu,h,hh,hE⟩:=between a b c _ _ hl
    (PairGapSigns.unequal_lower_negative a b c ha hb hbc)
    (harmonic_endpoint a b c ha hb0 hbc)
  have hu : 2*b*c/(b+c)<2*b := (div_lt_iff₀ hs).mpr (by nlinarith)
  exact ⟨e,hel,heu,by linarith,h,hh,hE⟩

theorem integer_tensor_root (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (H : ActualLaplacianIntegral (modulus p (pairExponents a b c)))
    (e : ℝ) (h : Fin 2 × Fin 2 → ℝ) (hh : h≠0)
    (hE : tensorK (a:ℝ) (b:ℝ) (c:ℝ)*ᵥh=e • h) : ∃ z : ℤ, e=z := by
  obtain ⟨z,hz⟩:=H _ (actual_paired_eigenvalue p hp hinj a b c ha hb hc e h hh hE)
  refine ⟨((((a+1)^2*(b+1)*(c+1)-2:ℕ):ℤ)+1-z),?_⟩
  push_cast
  linarith

theorem integer_det_zero (a b c : ℕ) (t : ℤ) (e : ℝ)
    (he : e=(a:ℝ)+1+(t:ℝ)) (h : Fin 2 × Fin 2 → ℝ) (hh : h≠0)
    (hE : tensorK (a:ℝ) (b:ℝ) (c:ℝ)*ᵥh=e • h) :
    (tensorK (a:ℤ) (b:ℤ) (c:ℤ)-((a:ℤ)+1+t) • 1).det=0 := by
  have hd : (tensorK (a:ℝ) (b:ℝ) (c:ℝ)-((a:ℝ)+1+(t:ℝ)) • 1).det=0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨h,hh,?_⟩
    rw [sub_mulVec,hE,he,smul_mulVec,one_mulVec,sub_self]
  rw [PairedIdealIntersectionDeterminants.det_tensorK_sub_scalar] at hd ⊢
  exact_mod_cast hd

/-- Full actual ideal-graph integrality forces one of the d-1 genuinely
nonzero quadratic tail equations, with its positive constant divisibility. -/
theorem actual_tail_candidate (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (H : ActualLaplacianIntegral (modulus p (pairExponents a b c))) :
    ∃ t : ℤ, 0<t ∧ t<((a:ℤ)+1)*b ∧
      (tensorK (a:ℤ) (b:ℤ) (c:ℤ)-((a:ℤ)+1+t) • 1).det=0 ∧
      (c:ℤ)∣PairTailArithmetic.H (a:ℤ) (b:ℤ) t := by
  obtain ⟨e,hel,heu,h,hh,hE⟩:=bounded_eigenpair (a:ℝ) (b:ℝ) (c:ℝ)
    (by positivity) (by positivity) (by exact_mod_cast (show 1≤c by omega))
  obtain ⟨z,hz⟩:=integer_tensor_root p hp hinj a b c ha hb hc H e h hh hE
  let t:=z-a-1
  have hlt : (0:ℝ)<(t:ℝ) := by dsimp [t]; push_cast; linarith
  have hut : (t:ℝ)<((a:ℝ)+1)*b := by dsimp [t]; push_cast; nlinarith
  have he : e=(a:ℝ)+1+(t:ℝ) := by dsimp [t]; push_cast; linarith
  have hd:=integer_det_zero a b c t e he h hh hE
  exact ⟨t,by exact_mod_cast hlt,by exact_mod_cast hut,hd,
    PairTailArithmetic.root_divides _ _ _ _ hd⟩

/-- Under b<c there is at most one positive candidate tail for each of
the b-1 offsets. The actual graph, not a scalar proxy, forces this offset. -/
theorem actual_harmonic_candidate (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 0<a) (hb : 0<b) (hbc : b<c)
    (H : ActualLaplacianIntegral (modulus p (pairExponents a b c))) :
    ∃ t : ℤ, (b:ℤ)<t ∧ t<2*b ∧ PairTailArithmetic.A (a:ℤ) (b:ℤ) t<0 ∧
      (tensorK (a:ℤ) (b:ℤ) (c:ℤ)-((a:ℤ)+1+t) • 1).det=0 := by
  have hc : 0<c := by omega
  obtain ⟨e,hel,_,heu,h,hh,hE⟩:=harmonic_eigenpair (a:ℝ) (b:ℝ) (c:ℝ)
    (by positivity) (by exact_mod_cast (show 1≤b by omega)) (by exact_mod_cast hbc)
  obtain ⟨z,hz⟩:=integer_tensor_root p hp hinj a b c ha hb hc H e h hh hE
  let t:=z-a-1
  have hlt : (b:ℝ)<(t:ℝ) := by dsimp [t]; push_cast; linarith
  have hut : (t:ℝ)<2*b := by dsimp [t]; push_cast; linarith
  have he : e=(a:ℝ)+1+(t:ℝ) := by dsimp [t]; push_cast; linarith
  have hd:=integer_det_zero a b c t e he h hh hE
  have hlI : (b:ℤ)<t := by exact_mod_cast hlt
  have huI : t<2*b := by exact_mod_cast hut
  refine ⟨t,hlI,huI,?_,hd⟩
  by_contra hA
  exact PairTailArithmetic.no_positive_root (a:ℤ) (b:ℤ) t (c:ℤ)
    (by exact_mod_cast (show 1≤a by omega)) hlI huI (by positivity) (le_of_not_gt hA) hd

end D5.S3.Combinatorics.SpectralGraph.PairTailSpectrum
