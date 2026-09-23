/- GID: D5/S3/Arith/Covering/Erdos203Lattice
   generality: I
   mirror-B: D5/B/S3/Arith/Covering/Erdos203Lattice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Index]
   utility: none
   digest: Exact base kernels, rectangular transversals and indices on the original period. -/

import D5.S3.Arith.Covering.Erdos203Normalization
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace D5.S3.Arith.Covering.Erdos203

/-- The integer homomorphism with the specified triangular basis columns. -/
def latticeMap (A C D : ℤ) : ℤ × ℤ →+ ℤ × ℤ where
  toFun z := (A*z.1+C*z.2,D*z.2)
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> dsimp <;> ring

/-- The six-row homogeneous lattice. -/
def sixLattice : AddSubgroup (ℤ × ℤ) := (latticeMap 360 228 24).range

/-- The seven-row homogeneous lattice. -/
def sevenLattice : AddSubgroup (ℤ × ℤ) := (latticeMap 3960 3108 24).range

/-- The literal rectangular representatives of a triangular lattice quotient. -/
def latticeCoset (A : ℕ) (C : ℤ) (q : Fin A × Fin 24) :
    (ℤ × ℤ) ⧸ (latticeMap A C 24).range := QuotientAddGroup.mk (q.1,q.2)

/-- The seven actual homogeneous rows determine the seven-row lattice. The specified
rectangles are complete transversals, their sizes are the exact indices, and both lattices
contain every full-period translate. -/
theorem base_lattice_geometry :
    (∀ x y : ℤ, (∀ i : Fin 7, (rows (i.castLE (by decide : 7 ≤ 252))).hits 0 x y) ↔
      (x,y) ∈ sevenLattice) ∧
    Function.Bijective (latticeCoset 360 228) ∧
    Function.Bijective (latticeCoset 3960 3108) ∧
    sixLattice.index = 8640 ∧ sevenLattice.index = 95040 ∧
    (∀ u v : ℤ, ((period : ℤ)*u,(period : ℤ)*v) ∈ sixLattice) ∧
    (∀ u v : ℤ, ((period : ℤ)*u,(period : ℤ)*v) ∈ sevenLattice) := by
  have sixmem (x y : ℤ) : (x,y) ∈ sixLattice ↔
      ∃ u v : ℤ, x=360*u+228*v ∧ y=24*v := by
    change (∃ z : ℤ × ℤ, (360*z.1+228*z.2,24*z.2)=(x,y)) ↔ _
    constructor
    · rintro ⟨⟨u,v⟩,heq⟩
      exact ⟨u,v,(congrArg Prod.fst heq).symm,(congrArg Prod.snd heq).symm⟩
    · rintro ⟨u,v,hx,hy⟩
      exact ⟨(u,v),Prod.ext hx.symm hy.symm⟩
  have sevenmem (x y : ℤ) : (x,y) ∈ sevenLattice ↔
      ∃ u v : ℤ, x=3960*u+3108*v ∧ y=24*v := by
    change (∃ z : ℤ × ℤ, (3960*z.1+3108*z.2,24*z.2)=(x,y)) ↔ _
    constructor
    · rintro ⟨⟨u,v⟩,heq⟩
      exact ⟨u,v,(congrArg Prod.fst heq).symm,(congrArg Prod.snd heq).symm⟩
    · rintro ⟨u,v,hx,hy⟩
      exact ⟨(u,v),Prod.ext hx.symm hy.symm⟩
  constructor
  · intro x y
    rw [sevenmem]
    constructor
    · intro h
      have h6 : ∀ i : Fin 6, (rows (i.castLE (by decide : 6 ≤ 252))).hits 0 x y :=
        fun i => h (i.castLE (by decide : 6 ≤ 7))
      obtain ⟨u,v,hx,hy⟩ := (six_row_kernel_coordinates x y).mp h6
      have h7 := h 6
      change (1*x+8*y)%11=0%11 at h7
      refine ⟨(u-8*v)/11,v,?_,hy⟩
      clear h h6
      omega
    · rintro ⟨u,v,rfl,rfl⟩ i
      by_cases hi : i.val < 6
      · exact (six_row_kernel_coordinates _ _).mpr
          ⟨11*u+8*v,v,by ring,rfl⟩ ⟨i.val,hi⟩
      · have : i=6 := by apply Fin.ext; omega
        subst i
        change (1*(3960*u+3108*v)+8*(24*v))%11=0%11
        omega
  have count (A : ℕ) (C : ℤ) (hA : 0 < A) :
      Function.Bijective (latticeCoset A C) ∧
      (latticeMap A C 24).range.index = A*24 := by
    let L := (latticeMap A C 24).range
    let f : Fin A × Fin 24 → (ℤ × ℤ) ⧸ L := latticeCoset A C
    have hbij : Function.Bijective f := by
      constructor
      · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩ ⟨⟨x',hx'⟩,⟨y',hy'⟩⟩ heq
        have hmem := QuotientAddGroup.eq_iff_sub_mem.mp heq
        rcases hmem with ⟨⟨u,v⟩,heq⟩
        have heqx := congrArg Prod.fst heq
        have heqy := congrArg Prod.snd heq
        change (A:ℤ)*u+C*v = (x:ℤ)-x' at heqx
        change 24*v = (y:ℤ)-y' at heqy
        have hv : v=0 := by omega
        simp only [hv,mul_zero,add_zero] at heqx
        have hu : u=0 := by
          have hAx : (x:ℤ)<A := by exact_mod_cast hx
          have hAx' : (x':ℤ)<A := by exact_mod_cast hx'
          have hpos : (0:ℤ)<A := by exact_mod_cast hA
          by_contra hu
          have hh : u ≤ -1 ∨ 1 ≤ u := by omega
          rcases hh with hh | hh <;> nlinarith [Int.natCast_nonneg x,Int.natCast_nonneg x']
        have ex : x=x' := by simp only [hu,mul_zero] at heqx; omega
        have ey : y=y' := by omega
        subst x' y'
        rfl
      · intro z
        induction z using Quotient.inductionOn with
        | h z =>
          let v := z.2/24
          let w := z.1-C*v
          let q : Fin A × Fin 24 :=
            (⟨(w%A).toNat,by
              have hpos : (0:ℤ)<A := by exact_mod_cast hA
              have hlt := Int.emod_lt_of_pos w hpos
              have hnonneg := Int.emod_nonneg w (ne_of_gt hpos)
              omega⟩,
             ⟨(z.2%24).toNat,by omega⟩)
          refine ⟨q,QuotientAddGroup.eq_iff_sub_mem.mpr ?_⟩
          refine ⟨(-(w/A),-v),?_⟩
          apply Prod.ext
          · change (A:ℤ)*(-(w/A))+C*(-v)=(q.1:ℤ)-z.1
            have hpos : (0:ℤ)<A := by exact_mod_cast hA
            have hw0 := Int.emod_nonneg w (ne_of_gt hpos)
            have hw := Int.emod_add_ediv_mul w A
            change (A:ℤ)*(-(w/A))+C*(-v)=↑((w%A).toNat)-z.1
            rw [Int.toNat_of_nonneg hw0]
            dsimp [w] at hw
            dsimp [w]
            nlinarith
          · change 24*(-v)=(q.2:ℤ)-z.2
            dsimp [q,v]
            omega
    refine ⟨hbij,?_⟩
    change Nat.card ((ℤ × ℤ) ⧸ L) = A*24
    rw [← Nat.card_congr (Equiv.ofBijective f hbij)]
    simp only [Nat.card_prod,Nat.card_fin]
  obtain ⟨bij6,index6⟩ := count 360 228 (by decide)
  obtain ⟨bij7,index7⟩ := count 3960 3108 (by decide)
  refine ⟨bij6,bij7,index6,index7,?_,?_⟩
  · intro u v
    apply (sixmem _ _).mpr
    refine ⟨48886437600*u-464421157200*v,733296564000*v,?_,?_⟩ <;>
      dsimp [period] <;> ring
  · intro u v
    apply (sevenmem _ _).mpr
    refine ⟨4444221600*u-575526697200*v,733296564000*v,?_,?_⟩ <;>
      dsimp [period] <;> ring

end D5.S3.Arith.Covering.Erdos203
