/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/LargePContinuous
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/LargePContinuous
   mirror-E: none(waiver:exact-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Unbounded a2 second peak LargePContinuous construction. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.ContinuousCover

/-! The same three exact chains, with the corrected all-h lower epsilon.

`chain8`, `chain16`, and `chain32` are imported from the canonical A2 module;
only their interval interpretation is re-proved here with
`5/(8*(z+1))-1/(8*64*z)`.  Thus no finite grid in p or h enters the proof.
-/
set_option autoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
open D5.S3.Combinatorics.Circle.FourNegative
open private basic_positive from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.Algebra

private def epsLoAll (z : ℚ) : ℚ := 5/(8*(z+1))-1/(8*64*z)
private def upperAll (z : ℚ) (r : CoverRow) : ℚ :=
  nominal r+r.j*epsLoAll z+1/8-etaMax z

open private Chain chain_hit chain8_indices chain16_indices chain32_indices
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.ContinuousCover

private theorem chain8_all : Chain (lower 8) (upperAll 8) 0 1 chain8 := by
  norm_num [chain8,Chain,lower,upperAll,nominal,epsLoAll,epsHi,etaMax]

private theorem chain16_all : Chain (lower 16) (upperAll 16) 0 1 chain16 := by
  norm_num [chain16,Chain,lower,upperAll,nominal,epsLoAll,epsHi,etaMax]

private theorem chain32_all : Chain (lower 32) (upperAll 32) 0 1 chain32 := by
  norm_num [chain32,Chain,lower,upperAll,nominal,epsLoAll,epsHi,etaMax]

private theorem continuous_cover_all (z eps eta x : ℚ)
    (hz : z=8 ∨ z=16 ∨ z=32)
    (heL : epsLoAll z≤eps) (heU : eps≤epsHi z)
    (heta : eta≤etaMax z) (hx : 0≤x) (hx' : x≤1) :
    ∃ j : ℕ, ∃ second : Bool, ∃ s : ℤ, j≤31 ∧
      (if second then 3/8+eta else eta) ≤ x+j*(5/8-eps)-s ∧
      x+j*(5/8-eps)-s ≤ (if second then 1/2-eta else 1/8-eta) := by
  have extract (rs : List CoverRow) (hc : Chain (lower z) (upperAll z) 0 1 rs)
      (hj : ∀ r∈rs, r.j≤31) :
      ∃ j : ℕ, ∃ second : Bool, ∃ s : ℤ, j≤31 ∧
        (if second then 3/8+eta else eta) ≤ x+j*(5/8-eps)-s ∧
        x+j*(5/8-eps)-s ≤ (if second then 1/2-eta else 1/8-eta) := by
    obtain ⟨r,hr,hl,hu⟩ := chain_hit (lower z) (upperAll z) rs 0 1 x hc hx hx'
    have hnon : (0:ℚ)≤r.j := by positivity
    have hl' := mul_le_mul_of_nonneg_left heU hnon
    have hu' := mul_le_mul_of_nonneg_left heL hnon
    refine ⟨r.j,r.second,r.shift,hj r hr,?_,?_⟩
    all_goals dsimp [lower,upperAll,nominal] at hl hu
    all_goals cases hs : r.second <;>
      simp only [hs,Bool.false_eq_true,ite_false,ite_true] at * <;> nlinarith
  rcases hz with rfl|rfl|rfl
  · exact extract chain8 chain8_all chain8_indices
  · exact extract chain16 chain16_all chain16_indices
  · exact extract chain32 chain32_all chain32_indices

private theorem continuous_parameter_bounds_all (p q h : ℤ) (hp : 64≤p)
    (hq : q=2 ∨ q=4 ∨ q=8) (hh : 1≤h) :
    epsLoAll (4*q) ≤ (D p q h:ℚ)/(8*(A p q h:ℚ)) ∧
    (D p q h:ℚ)/(8*(A p q h:ℚ)) ≤ epsHi (4*q) ∧
    ((1+124*h*Q q:ℤ):ℚ)/(8*(A p q h:ℚ)) ≤ etaMax (4*q) := by
  have hq2 : 2≤q := by omega
  have hAi : 0<A p q h :=
    (basic_positive p q h (by omega) hq2 hh).1
  have hden : (0:ℚ)<8*(A p q h:ℚ) := by
    exact mul_pos (by norm_num) (by exact_mod_cast hAi)
  obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ p=u+64 := ⟨p-64,by omega,by ring⟩
  obtain ⟨t,ht,rfl⟩ : ∃ t : ℤ, 0≤t ∧ h=t+1 := ⟨h-1,by omega,by ring⟩
  rcases hq with rfl|rfl|rfl
  all_goals refine ⟨(le_div_iff₀ hden).2 ?_,
    (div_le_iff₀ hden).2 ?_,(div_le_iff₀ hden).2 ?_⟩
  all_goals
    push_cast
    norm_num [epsLoAll,epsHi,etaMax,D,A,L,Q,
      SecondPeakHighD.A,SecondPeakHighD.L,SecondPeakHighD.Z,
      SecondPeakHighD.T,SecondPeakHighD.Y]
    push_cast
    apply le_of_sub_nonneg
    ring_nf
    positivity

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
