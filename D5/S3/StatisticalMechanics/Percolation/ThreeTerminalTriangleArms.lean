/- GID: D5/S3/StatisticalMechanics/Percolation/ThreeTerminalTriangleArms
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/ThreeTerminalTriangleArms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A central triangle and three independent arms satisfy the constant-two bound. -/

import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond

/-! The complete six-edge network needed by a cactus central-cycle reduction. -/

namespace D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms
open ThreeTerminalBond
open scoped BigOperators
set_option backward.isDefEq.respectTransparency.types false

/-- Central ports are 3,4,5; terminals 0,1,2 have distinct pendant arms. -/
def triangleArmsEnds : Fin 6 → Fin 6 × Fin 6 :=
  ![(3,4),(4,5),(3,5),(0,3),(1,4),(2,5)]

private lemma arms_partition (ω : Fin 6 → Bool) :
    partition triangleArmsEnds 0 1 2 ω =
      if ω 3 && ω 4 && (ω 0 || (ω 2 && ω 1)) then
        (if ω 4 && ω 5 && (ω 1 || (ω 0 && ω 2)) then .all else .ab)
      else if ω 4 && ω 5 && (ω 1 || (ω 0 && ω 2)) then .bc
      else if ω 3 && ω 5 && (ω 2 || (ω 0 && ω 1)) then .ac else .separate := by
  revert ω
  decide +kernel

private lemma cube_three : (Finset.univ : Finset (Fin 3 → Bool)) =
    {![false,false,false],![false,false,true],![false,true,false],![false,true,true],
     ![true,false,false],![true,false,true],![true,true,false],![true,true,true]} := by decide

/-- Full five-law preservation, computed from the actual sixty-four open subgraphs. -/
theorem triangle_arms_law (u v s A B C : ℝ) :
    let U := u+(1-u)*s*v
    let V := v+(1-v)*u*s
    let W := s+(1-s)*u*v
    let K := u*v+u*s+v*s-2*u*v*s
    law triangleArmsEnds 0 1 2 ![u,v,s,A,B,C] = fun mode => match mode with
      | .separate => 1-A*B*U-B*C*V-A*C*W+2*A*B*C*K
      | .ab => A*B*U-A*B*C*K
      | .bc => B*C*V-A*B*C*K
      | .all => A*B*C*K
      | .ac => A*C*W-A*B*C*K := by
  dsimp only
  funext mode
  unfold law
  simp only [arms_partition]
  rw [← (Fin.appendEquiv (α:=Bool) 3 3).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.appendEquiv_apply,cube_three]
  cases mode <;> norm_num [weight,Fin.prod_univ_succ,Fin.append,Fin.addCases] <;> ring

/-- The full arm transformation retains the exceptional mass, the first-arm
correction and the second-terminal correction in the same source law. -/
theorem triangle_arms_factorization (u v s A B C : ℝ) :
    let K := u*v+u*s+v*s-2*u*v*s
    let L := (1-s)*(u+v-u*v)
    let Z₀ := s*(1-u)*(1-v)
    let S := A*C
    law triangleArmsEnds 0 1 2 ![u,v,s,A,B,C] .ac = S*(Z₀+(1-B)*K) ∧
    delta (law triangleArmsEnds 0 1 2 ![u,v,s,A,B,C]) =
      B^2*S*Z₀*(L+(1-S)*K)+B*(1-B)*S*K*(1-S*(Z₀+K)) := by
  dsimp only
  rw [triangle_arms_law]
  simp only [delta]
  constructor <;> ring

/-- All six independent edge rates, including every deterministic boundary. -/
theorem triangle_arms_bound (u v s A B C : ℝ) (hu : u ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc 0 1) (hs : s ∈ Set.Icc 0 1) (hA : A ∈ Set.Icc 0 1)
    (hB : B ∈ Set.Icc 0 1) (hC : C ∈ Set.Icc 0 1) :
    0 ≤ delta (law triangleArmsEnds 0 1 2 ![u,v,s,A,B,C]) ∧
    delta (law triangleArmsEnds 0 1 2 ![u,v,s,A,B,C]) ≤
      2*law triangleArmsEnds 0 1 2 ![u,v,s,A,B,C] .ac := by
  let K := u*v+u*s+v*s-2*u*v*s
  let L := (1-s)*(u+v-u*v)
  let Z₀ := s*(1-u)*(1-v)
  let S := A*C
  have hu0 := hu.1
  have hv0 := hv.1
  have hs0 := hs.1
  have hA0 := hA.1
  have hB0 := hB.1
  have hC0 := hC.1
  have hu' : 0 ≤ 1-u := sub_nonneg.mpr hu.2
  have hv' : 0 ≤ 1-v := sub_nonneg.mpr hv.2
  have hs' : 0 ≤ 1-s := sub_nonneg.mpr hs.2
  have hB' : 0 ≤ 1-B := sub_nonneg.mpr hB.2
  have hS0 : 0 ≤ S := mul_nonneg hA.1 hC.1
  have hS1 : S ≤ 1 := mul_le_one₀ hA.2 hC.1 hC.2
  have hK : 0 ≤ K := by
    calc 0 ≤ u*v*(1-s)+u*s*(1-v)+v*s*(1-u)+u*v*s := by positivity
         _ = K := by dsimp [K]; ring
  have hZ : 0 ≤ Z₀ := mul_nonneg (mul_nonneg hs.1 hu') hv'
  have hL : 0 ≤ L := by
    apply mul_nonneg hs'
    nlinarith [mul_nonneg hu' hv.1]
  have hR0 : 0 ≤ L+(1-S)*K :=
    add_nonneg hL (mul_nonneg (sub_nonneg.mpr hS1) hK)
  have hR2 : L+(1-S)*K ≤ 2 := by
    have he : L+(1-S)*K = u+v-s*u*v-S*K := by dsimp [L,K]; ring
    rw [he]
    nlinarith [mul_nonneg (mul_nonneg hs.1 hu.1) hv.1,mul_nonneg hS0 hK,hu.2,hv.2]
  have hW0 : 0 ≤ Z₀+K := add_nonneg hZ hK
  have hW1 : Z₀+K ≤ 1 := by
    have huv : u*v ≤ 1 := mul_le_one₀ hu.2 hv.1 hv.2
    calc Z₀+K = s+(1-s)*(u*v) := by dsimp [Z₀,K]; ring
         _ ≤ s+(1-s)*1 := add_le_add_right (mul_le_mul_of_nonneg_left huv hs') s
         _ = 1 := by ring
  have hSW : S*(Z₀+K) ≤ 1 := mul_le_one₀ hS1 hW0 hW1
  have hQ : 0 ≤ (1-B)*S*K := mul_nonneg (mul_nonneg hB' hS0) hK
  have hcoef : B*(1-S*(Z₀+K)) ≤ 1 := by
    have hn := mul_nonneg hS0 hW0
    nlinarith [mul_nonneg hB0 hn,hB.2]
  have hsecond : B*(1-B)*S*K*(1-S*(Z₀+K)) ≤ (1-B)*S*K := by
    nlinarith only [mul_le_of_le_one_right hQ hcoef]
  have hB2 : B^2 ≤ 1 := by nlinarith [hB.1,hB.2]
  have hfirstCoef : B^2*(L+(1-S)*K) ≤ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hB2) hR0]
  have hfirst : B^2*S*Z₀*(L+(1-S)*K) ≤ 2*S*Z₀ := by
    nlinarith only [mul_le_mul_of_nonneg_left hfirstCoef (mul_nonneg hS0 hZ)]
  obtain ⟨hZeq,hDeq⟩ := triangle_arms_factorization u v s A B C
  change law triangleArmsEnds 0 1 2 ![u,v,s,A,B,C] .ac = S*(Z₀+(1-B)*K) at hZeq
  change delta (law triangleArmsEnds 0 1 2 ![u,v,s,A,B,C]) =
    B^2*S*Z₀*(L+(1-S)*K)+B*(1-B)*S*K*(1-S*(Z₀+K)) at hDeq
  rw [hDeq,hZeq]
  constructor
  · have hSW0 : 0 ≤ 1-S*(Z₀+K) := sub_nonneg.mpr hSW
    positivity
  · nlinarith only [hfirst,hsecond,hQ]

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms.triangle_arms_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms triangle_arms_law
/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms.triangle_arms_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms triangle_arms_factorization
/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms.triangle_arms_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms triangle_arms_bound

end D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms
