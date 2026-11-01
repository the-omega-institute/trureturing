/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Source
   generality: I
   mirror-B: none(waiver:private-consumed-full-saddle-implementation)
   mirror-E: none(waiver:private-consumed-full-saddle-implementation)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Eight exact source recurrences, odd representatives and centered successor bounds. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle.Structure
import D5.S3.Combinatorics.Circle.FourNegative.Descending.Endpoint

/-! SOURCE_ONLY_UNCOMPILED. All rows, offsets and lengths are those of the existing
PacketNormalForm.Source, whose chain_values consumes MaxPlusTwo.SourceTable.source_table.
We retain that concrete source, rather than posit a second realization.
For x=2^a,y=2^b,z=2^c,t=2^d,N=xyzt-1,Q=2N+1, the recurrences below are
 tA=N+B, zB=N+L, yL=N+M, xM=N+A;
 t(2A)=Q+Bn, zBn=Q+Ln, yLn=Q+Mn, xMn=Q+A.
All successors are positive odd and at most modulus-2. Consequently the last
positive ladder term (modulus+successor)/4 lies in the centered half strip.
Actual ladder reduction and the literal fresh value A are reused via chain_values. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle
open SourceWidth PeriodicShortening RunFirstEarTransport
open private sourceMod base newBase charge chainLength nextBase nextNewBase
  chain_values new_base_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private half_power from D5.S3.Combinatorics.Circle.FourNegative.Descending.Endpoint

private theorem source_recurrences (a b c d : ℕ) :
    ∀ j : Fin 4,
      (2:ℤ)^(chainLength a b c d j)*base a b c d j =
        sourceMod a b c d+nextBase a b c d j ∧
      (2:ℤ)^(chainLength a b c d j)*newBase a b c d j =
        (2*sourceMod a b c d+1)+nextNewBase a b c d j := by
  intro j
  fin_cases j <;>
    dsimp [chainLength,base,newBase,charge,sourceMod,nextBase,nextNewBase] <;>
    constructor <;> ring

private theorem source_parity (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) :
    sourceMod a b c d%2=1 ∧
    (∀ j : Fin 4, base a b c d j%2=1) ∧
    (∀ j : Fin 4, nextNewBase a b c d j%2=1) := by
  have even (n : ℕ) (hn : 1≤n) : (2:ℤ)^n%2=0 := by
    rw [half_power n hn]
    omega
  have hpa := even a (by omega)
  have hpb := even b (by omega)
  have hpc := even c (by omega)
  have hpd := even d (by omega)
  refine ⟨?_,?_,?_⟩
  · simp [sourceMod,Int.sub_emod,Int.mul_emod,hpa,hpb,hpc,hpd]
  · intro j
    fin_cases j <;>
      simp [base,Int.add_emod,Int.mul_emod,hpa,hpb,hpc,hpd]
  · intro j
    fin_cases j <;>
      simp [nextNewBase,newBase,base,charge,Int.add_emod,Int.sub_emod,Int.mul_emod,hpa,hpb,hpc,hpd]

private theorem source_centered_bounds (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) :
    ∀ j : Fin 4,
      (1≤base a b c d j ∧ base a b c d j≤sourceMod a b c d-2) ∧
      (1≤newBase a b c d j ∧ newBase a b c d j≤(2*sourceMod a b c d+1)-2) := by
  have p := source_parity a b c d ha hb hc hd
  have old := (chain_values a b c d ha hb hc hd).1
  have new := new_base_bounds a b c d ha hb hc hd
  intro j
  have ho := old j
  have hn := new j
  have po := p.2.1 j
  have pm := p.1
  have upper : base a b c d j≤sourceMod a b c d-2 := by omega
  have charge_nonneg : 0≤charge b c j := by
    fin_cases j <;> dsimp [charge] <;> positivity
  refine ⟨⟨ho.1,upper⟩,hn.1,?_⟩
  dsimp only [newBase]
  omega

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle
