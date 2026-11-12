/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakResidualTails/C3DiagonalPhysicalGates
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakResidualTails/C3DiagonalPhysicalGates
   mirror-E: none(waiver:physical-dependent-source-registration)
   anchors: [lake/module/D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source]
   utility: none
   digest: Canonical signed terminals and bank masses transport gates to physical labels. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.PhysicalMasses
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.C3Gates
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.DiagonalGates

/-! Canonical signed terminals and bank masses transport gates to physical labels. Original source owners supply the reused proofs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
open private sourceMod charge nextBase nextNewBase chain_values source_totals from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open scoped BigOperators
open PacketNormalForm

/-- Actual Finset mass; the first index of M is the physical bank. -/
noncomputable def physicalOldMass (a b c d : ℕ) (M : Fin 4 → Fin 4 → ℕ)
    (row : Fin 4) : ℤ :=
  ∑ i ∈ physicalBank a b c d M row, oldValue a b c d i

noncomputable def physicalNewMass (a b c d : ℕ) (M : Fin 4 → Fin 4 → ℕ)
    (row : Fin 4) : ℤ :=
  ∑ i ∈ physicalBank a b c d M row, newValue a b c d i

/-- The five actual old row boundaries, including the empty prefix. -/
noncomputable def physicalOldBoundary (a b c d : ℕ)
    (M : Fin 4 → Fin 4 → ℕ) (order : Fin 4 → Fin 4) : Fin 5 → ℤ :=
  let s := fun row => physicalOldMass a b c d M row +
    oldValue a b c d (terminalLabel a b c d (order row))
  ![0, s 0, s 0+s 1, s 0+s 1+s 2, s 0+s 1+s 2+s 3]

/-- Shift by the actual fresh label at the literal cut 0. The terminal
    uses order(row); the mass still uses row, not order(row). -/
noncomputable def physicalNewBoundary (a b c d : ℕ)
    (M : Fin 4 → Fin 4 → ℕ) (order : Fin 4 → Fin 4) : Fin 5 → ℤ :=
  let E := newValue a b c d (size a b c d)
  let s := fun row => physicalNewMass a b c d M row +
    newValue a b c d (terminalLabel a b c d (order row))
  ![E, E+s 0, E+s 0+s 1, E+s 0+s 1+s 2, E+s 0+s 1+s 2+s 3]

/-- Concrete sides for the original residual banks and literal cut 0.
    No bound is an input. Totals refer to the actual physical words. -/
def ActualPhysicalGateSides (a b c d : ℕ) : Prop :=
  let M := residualBanks a b c d
  let order := residualOrder c d
  let H := physicalOldBoundary a b c d M order
  let G := physicalNewBoundary a b c d M order
  let word := physicalWord a b c d M order
  cut0 = 0 ∧
    physicalEarWord a b c d = size a b c d :: word ∧
    H 0 = 0 ∧ G 0 = base a b c d 0 ∧ H 4 = 0 ∧ G 4 = 0 ∧
    (∀ row : Fin 4, 0 ≤ H row.succ) ∧
    (∀ row : Fin 4,
      G row.castSucc + physicalNewMass a b c d M row ≤ sourceMod a b c d) ∧
    (word.map (oldValue a b c d)).sum = 0 ∧
    (word.map (newValue a b c d)).sum = -base a b c d 0 ∧
    newValue a b c d (size a b c d) = base a b c d 0 ∧
    ((physicalEarWord a b c d).map (newValue a b c d)).sum = 0

-- These two private expressions match the PUBLIC scalar gate theorem types.
-- They are only consumed by the actual-physical transport below.
private def scalarOldBoundary (a b c d : ℕ) (M : Fin 4 → Fin 4 → ℕ) :
    Fin 5 → ℤ :=
  let F := base a b c d
  let N := sourceMod a b c d
  let m := fun row => ∑ chain : Fin 4, (M row chain : ℤ) * F chain
  ![0, 2*m 0+F 1-N,
    2*(m 0+m 1)+F 1+F 0-2*N,
    2*(m 0+m 1+m 2)+F 1+F 0+F 3-3*N,
    2*(m 0+m 1+m 2+m 3)+F 1+F 0+F 3+F 2-4*N]

private def scalarNewBoundary (a b c d : ℕ) (M : Fin 4 → Fin 4 → ℕ) :
    Fin 5 → ℤ :=
  let F := newBase a b c d
  let A := base a b c d 0
  let Q := 2*sourceMod a b c d+1
  let n := fun row => ∑ chain : Fin 4, (M row chain : ℤ) * F chain
  ![2*A, 2*A+2*n 0+F 1-Q,
    2*A+2*(n 0+n 1)+F 1+A-2*Q,
    2*A+2*(n 0+n 1+n 2)+F 1+A+F 3-3*Q,
    2*A+2*(n 0+n 1+n 2+n 3)+F 1+A+F 3+F 2-4*Q]

private def canonicalDoubledSides (a b c d : ℕ) (M : Fin 4 → Fin 4 → ℕ) : Prop :=
  scalarOldBoundary a b c d M 4 = 0 ∧
    scalarNewBoundary a b c d M 4 = 0 ∧
    (∀ row : Fin 4, 0 ≤ scalarOldBoundary a b c d M row.succ) ∧
    (∀ row : Fin 4, scalarNewBoundary a b c d M row.castSucc +
      2*(∑ chain : Fin 4, (M row chain : ℤ)*newBase a b c d chain) ≤
        2*sourceMod a b c d)

/-- Signed division transport for the ORIGINAL centered values. The last
    matched-new successor is nextNewBase 3 = OLD base 0. -/
private theorem terminal_doubles (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) :
    (∀ r : Fin 4, 2*oldValue a b c d (terminalLabel a b c d r) =
      nextBase a b c d r - sourceMod a b c d) ∧
    (∀ r : Fin 4, 2*newValue a b c d (terminalLabel a b c d r) =
      nextNewBase a b c d r - (2*sourceMod a b c d+1)) ∧
    newValue a b c d (size a b c d) = base a b c d 0 := by
  have hv := chain_values a b c d ha hb hc hd
  have hp (n : ℕ) (hn : 2 ≤ n) : (2 : ℤ)^n % 2 = 0 := by
    calc
      (2 : ℤ)^n % 2 = ((2 : ℤ)^((n-1)+1)) % 2 := by
        exact congrArg (fun k : ℕ => (2 : ℤ)^k % 2)
          (show n = (n-1)+1 by omega)
      _ = 0 := by rw [pow_succ]; simp [Int.mul_emod]
  have hparOld (r : Fin 4) :
      (nextBase a b c d r-sourceMod a b c d) % 2 = 0 := by
    fin_cases r <;>
      simp [nextBase, base, sourceMod, Int.add_emod, Int.sub_emod,
        Int.mul_emod, hp a ha, hp b hb, hp c hc, hp d hd]
  have hparNew (r : Fin 4) :
      (nextNewBase a b c d r-(2*sourceMod a b c d+1)) % 2 = 0 := by
    fin_cases r <;>
      simp [nextNewBase, newBase, charge, base, sourceMod,
        Int.add_emod, Int.sub_emod, Int.mul_emod,
        hp a ha, hp b hb, hp c hc, hp d hd]
  have hlength (r : Fin 4) : 2 ≤ chainLength a b c d r := by
    fin_cases r
    · simpa [chainLength] using hd
    · simpa [chainLength] using hc
    · simpa [chainLength] using hb
    · simpa [chainLength] using ha
  have hlabel (r : Fin 4) : terminalLabel a b c d r =
      chainStart b c d r + (chainLength a b c d r-1) := by
    have := hlength r
    dsimp only [terminalLabel]
    omega
  refine ⟨?_, ?_, hv.2.2.2⟩
  · intro r
    have hl := hlength r
    have hi : chainLength a b c d r-1 < chainLength a b c d r := by omega
    have hn : ¬ (chainLength a b c d r-1)+1 < chainLength a b c d r := by omega
    rw [hlabel r, hv.2.1 r _ hi, if_neg hn]
    have hm := hparOld r
    omega
  · intro r
    have hl := hlength r
    have hi : chainLength a b c d r-1 < chainLength a b c d r := by omega
    have hn : ¬ (chainLength a b c d r-1)+1 < chainLength a b c d r := by omega
    rw [hlabel r, hv.2.2.1 r _ hi, if_neg hn]
    have hm := hparNew r
    omega

/-- Actual masses, actual signed terminal drops and the fresh source phase
    identify EVERY doubled boundary, including both starting boundaries. -/
private theorem physical_boundary_transport (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (M : Fin 4 → Fin 4 → ℕ)
    (hinv : ∀ chain, MaskInventory (chainLength a b c d chain-1)
      (fun bank => M bank chain)) :
    (∀ row, physicalOldMass a b c d M row =
      ∑ chain : Fin 4, (M row chain : ℤ)*base a b c d chain) ∧
    (∀ row, physicalNewMass a b c d M row =
      ∑ chain : Fin 4, (M row chain : ℤ)*newBase a b c d chain) ∧
    (∀ i : Fin 5, 2*physicalOldBoundary a b c d M normalOrder i =
      scalarOldBoundary a b c d M i) ∧
    (∀ i : Fin 5, 2*physicalNewBoundary a b c d M normalOrder i =
      scalarNewBoundary a b c d M i) := by
  have hm (row : Fin 4) : physicalOldMass a b c d M row =
      ∑ chain : Fin 4, (M row chain : ℤ)*base a b c d chain := by
    simpa only [physicalOldMass, mul_comm] using
      (physical_masses a b c d ha hb hc hd M hinv row).1
  have hn (row : Fin 4) : physicalNewMass a b c d M row =
      ∑ chain : Fin 4, (M row chain : ℤ)*newBase a b c d chain := by
    simpa only [physicalNewMass, mul_comm] using
      (physical_masses a b c d ha hb hc hd M hinv row).2
  obtain ⟨hf,hg,hfresh⟩ := terminal_doubles a b c d ha hb hc hd
  have hf0 := hf 0; have hf1 := hf 1; have hf2 := hf 2; have hf3 := hf 3
  have hg0 := hg 0; have hg1 := hg 1; have hg2 := hg 2; have hg3 := hg 3
  simp [nextBase] at hf0 hf1 hf2 hf3
  simp [nextNewBase] at hg0 hg1 hg2 hg3
  refine ⟨hm, hn, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      simp [physicalOldBoundary, scalarOldBoundary, hm, normalOrder] <;> omega
  · intro i
    fin_cases i <;>
      simp [physicalNewBoundary, scalarNewBoundary, hn, hfresh, normalOrder] <;> omega

-- This is a consumed transport lemma. Its gate input is discharged below
-- by the two supplied public universal gate theorems, never exported as an
-- extra hypothesis of the actual-domain conclusion.
private theorem actual_sides_of_doubled (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (hdom : OriginalDomain a b c d)
    (horder : residualOrder c d = normalOrder)
    (hgates : canonicalDoubledSides a b c d (residualBanks a b c d)) :
    ActualPhysicalGateSides a b c d := by
  let M := residualBanks a b c d
  have ht := physical_boundary_transport a b c d ha hb hc hd M
    (residual_inventory a b c d hdom)
  dsimp only [M] at ht
  dsimp only [canonicalDoubledSides] at hgates
  obtain ⟨hO,hG,hLower,hUpper⟩ := hgates
  have htO := ht.2.2.1
  have htG := ht.2.2.2
  have htot := source_totals a b c d ha hb hc hd
  have hp : (physicalWord a b c d M (residualOrder c d)).Perm
      (List.range (size a b c d)) :=
    Multiset.coe_eq_coe.mp (original_physical_partition a b c d hdom)
  have htotalOld : ((physicalWord a b c d M (residualOrder c d)).map
      (oldValue a b c d)).sum = 0 :=
    (hp.map (oldValue a b c d)).sum_eq.trans htot.1
  have htotalMatched : ((physicalWord a b c d M (residualOrder c d)).map
      (newValue a b c d)).sum = -base a b c d 0 :=
    (hp.map (newValue a b c d)).sum_eq.trans htot.2.1
  have hear : physicalEarWord a b c d =
      size a b c d :: physicalWord a b c d M (residualOrder c d) := by
    simp [physicalEarWord, cut0, earSlot0, insertAt, M]
  dsimp only [ActualPhysicalGateSides]
  refine ⟨rfl, hear, ?_, ?_, ?_, ?_, ?_, ?_,
    htotalOld, htotalMatched, htot.2.2, ?_⟩
  · simp [physicalOldBoundary]
  · simpa [physicalNewBoundary] using htot.2.2
  · rw [horder]
    have hh := htO 4
    omega
  · rw [horder]
    have hh := htG 4
    omega
  · intro row
    rw [horder]
    have hh := htO row.succ
    have hs := hLower row
    omega
  · intro row
    rw [horder]
    have hh := htG row.castSucc
    have hm := ht.2.1 row
    have hs := hUpper row
    omega
  · rw [hear, List.map_cons, List.sum_cons, htot.2.2, htotalMatched]
    ring

private theorem c3_canonical_gates (b d : ℕ) (hd : 7 ≤ d) (hb : d < b) :
    canonicalDoubledSides 5 b 3 d (c3Banks (d-5) (b-d-1)) := by
  let e := d-5
  let ell := b-d-1
  let h : ℤ := ((2^e : ℕ) : ℤ)
  let t : ℤ := ((2^ell : ℕ) : ℤ)
  let x : ℤ := 32
  let z : ℤ := 8
  let w := 32*h
  let y := 64*h*t
  let A := 1+x+x*y+x*y*z
  let B := 1+w+w*x+w*x*y
  let L := 1+z+w*z+w*z*x
  let K := 1+y+y*z+y*w*z
  let N := x*y*z*w-1
  have he : 2 ≤ e := by dsimp [e]; omega
  have hdEq : d = e+5 := by dsimp [e]; omega
  have hbEq : b = e+ell+6 := by dsimp [e, ell]; omega
  have hw : (2 : ℤ)^d = w := by
    calc
      (2 : ℤ)^d = 2^(e+5) := congrArg (fun n => (2 : ℤ)^n) hdEq
      _ = w := by norm_num [pow_add, w, h] <;> ring
  have hy : (2 : ℤ)^b = y := by
    calc
      (2 : ℤ)^b = 2^(e+ell+6) := congrArg (fun n => (2 : ℤ)^n) hbEq
      _ = y := by norm_num [pow_add, y, h, t] <;> ring
  have hx : (2 : ℤ)^5 = x := by norm_num [x]
  have hz : (2 : ℤ)^3 = z := by norm_num [z]
  have hbase : base 5 b 3 d = (![A,B,L,K] : Fin 4 → ℤ) := by
    funext r
    fin_cases r <;> simp only [base, Matrix.cons_val_zero, Matrix.cons_val_succ,
      hx, hy, hz, hw] <;> dsimp [A, B, L, K] <;> ring
  have hnew : newBase 5 b 3 d =
      (![2*A,2*B-1,2*L-z-1,2*K-y*(z+1)-1] : Fin 4 → ℤ) := by
    funext r
    fin_cases r <;> simp [newBase, hbase, charge, hy, hz] <;> ring
  have hmod : sourceMod 5 b 3 d = N := by
    simp only [sourceMod, hx, hy, hz, hw]
    rfl
  have hs := c3_doubled_gates e ell he
  simpa [canonicalDoubledSides, scalarOldBoundary, scalarNewBoundary,
    hbase, hnew, hmod, A, B, L, K, N, x, y, z, w, h, t, e, ell] using hs

private theorem diagonal_canonical_gates (b c d : ℕ)
    (hc : 3 ≤ c) (hd : 2*c ≤ d) (hb : d < b) :
    canonicalDoubledSides (c+1) b c d
      (diagonalBanks c (d-2*c) (b-d-1)) := by
  let delta := d-2*c
  let ell := b-d-1
  let e := diagonalExponent c delta
  let z : ℤ := ((2^c : ℕ) : ℤ)
  let h : ℤ := (diagonalH c delta : ℤ)
  let t : ℤ := ((2^ell : ℕ) : ℤ)
  let x := 2*z
  let w := 2*z*h
  let y := 4*z*h*t
  let A := 1+x+x*y+x*y*z
  let B := 1+w+w*x+w*x*y
  let L := 1+z+w*z+w*z*x
  let K := 1+y+y*z+y*w*z
  let N := x*y*z*w-1
  have he : 2 ≤ e := by dsimp [e, diagonalExponent]; omega
  have hdOriginal : d = 2*c+delta := by dsimp [delta]; omega
  have hbOriginal : b = d+1+ell := by dsimp [ell]; omega
  have hdEq : d = c+e+1 := by
    dsimp [e, diagonalExponent]
    omega
  have hbEq : b = c+e+ell+2 := by omega
  have hx : (2 : ℤ)^(c+1) = x := by
    rw [pow_succ]
    dsimp [x, z]
    push_cast
    ring
  have hz : (2 : ℤ)^c = z := by simp [z]
  have hh : (2 : ℤ)^e = h := by simp [h, diagonalH, e]
  have hw : (2 : ℤ)^d = w := by
    calc
      (2 : ℤ)^d = 2^(c+e+1) := congrArg (fun n => (2 : ℤ)^n) hdEq
      _ = w := by
        simp only [pow_add, hz, hh]
        norm_num <;> dsimp [w] <;> ring
  have hy : (2 : ℤ)^b = y := by
    calc
      (2 : ℤ)^b = 2^(c+e+ell+2) := congrArg (fun n => (2 : ℤ)^n) hbEq
      _ = y := by
        simp only [pow_add, hz, hh]
        norm_num [y, t] <;> ring
  have hbase : base (c+1) b c d = (![A,B,L,K] : Fin 4 → ℤ) := by
    funext r
    fin_cases r <;> simp only [base, Matrix.cons_val_zero, Matrix.cons_val_succ,
      hx, hy, hz, hw] <;> dsimp [A, B, L, K] <;> ring
  have hnew : newBase (c+1) b c d =
      (![2*A,2*B-1,2*L-z-1,2*K-y*(z+1)-1] : Fin 4 → ℤ) := by
    funext r
    fin_cases r <;> simp [newBase, hbase, charge, hy, hz] <;> ring
  have hmod : sourceMod (c+1) b c d = N := by
    simp only [sourceMod, hx, hy, hz, hw]
    rfl
  have hs := diagonal_doubled_gates c delta ell hc
  simpa [canonicalDoubledSides, scalarOldBoundary, scalarNewBoundary,
    hbase, hnew, hmod, A, B, L, K, N, x, y, z, w, h, t, e, ell] using hs

/-- Full original C3 and diagonal cones, actual banks, original centered
    phases, order [0,3,2,1], literal cut 0 and separate physical totals.
    This delivers the two missing gate SIDES only, not a certificate. -/
theorem c3_diagonal_physical_gates (a b c d : ℕ) (hb : d < b)
    (hshape : (c = 3 ∧ a = 5 ∧ 7 ≤ d) ∨
      (3 ≤ c ∧ a = c+1 ∧ 2*c ≤ d)) :
    ActualPhysicalGateSides a b c d := by
  rcases hshape with h3 | hdiag
  · obtain ⟨rfl,rfl,hd⟩ := h3
    have hdom : OriginalDomain 5 b 3 d := ⟨hb, Or.inr (Or.inr ⟨rfl,rfl,hd⟩)⟩
    apply actual_sides_of_doubled 5 b 3 d (by omega) (by omega)
      (by omega) (by omega) hdom (by simp [residualOrder])
    simpa only [residualBanks, show ¬ (3 : ℕ) = 2 by omega,
      show ¬ (5 : ℕ) = 3+1 by omega, ite_false] using c3_canonical_gates b d hd hb
  · obtain ⟨hc,rfl,hd⟩ := hdiag
    have hc2 : c ≠ 2 := by omega
    have hdom : OriginalDomain (c+1) b c d :=
      ⟨hb, Or.inr (Or.inl ⟨hc,rfl,hd⟩)⟩
    apply actual_sides_of_doubled (c+1) b c d (by omega) (by omega)
      (by omega) (by omega) hdom (by simp [residualOrder, hc2])
    simpa only [residualBanks, hc2, ite_false, ite_true] using
      diagonal_canonical_gates b c d hc hd hb

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
