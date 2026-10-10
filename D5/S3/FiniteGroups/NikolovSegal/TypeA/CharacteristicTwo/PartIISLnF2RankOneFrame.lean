/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2RankOneFrame
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2RankOneFrame
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo.PartIISLnF2PivotPath
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace NikolovSegal.SLnF2Bare
open Matrix NikolovSegal.SLnRootAction NikolovSegal.SLnFullGroup
open NikolovSegal.SLnNormalizer NikolovSegal.SLnF2Residual
universe u
variable {F : Type u} [Field F] [Fintype F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F
abbrev frameVector (X : Fin (n-1) → G) (i : Fin (n-1)) (a : Fin n) : F :=
  deviation (X i) a (simpleRoot i).val.2
abbrev frameCovector (X : Fin (n-1) → G) (i : Fin (n-1)) (b : Fin n) : F :=
  deviation (X i) (simpleRoot i).val.1 b
noncomputable def framePairing (X : Fin (n-1) → G) (i j : Fin (n-1)) : F :=
  ∑ k : Fin n, frameCovector X i k*frameVector X j k

theorem frame_factor (X : Fin (n-1) → G)
    (hm : ∀ i a b d e, deviation (X i) a b*deviation (X i) d e=deviation (X i) a e*deviation (X i) d b)
    (hp : ∀ i, simpleEntry (X i) i=1) (i : Fin (n-1)) (a b : Fin n) :
    deviation (X i) a b=frameVector X i a*frameCovector X i b := by
  have he := hm i a b (simpleRoot i).val.1 (simpleRoot i).val.2
  rw [deviation_simple,hp,mul_one] at he
  exact he

theorem frame_vector_pivot (X : Fin (n-1) → G) (hp : ∀ i, simpleEntry (X i) i=1) (i : Fin (n-1)) :
    frameVector X i (simpleRoot i).val.1=1 := by rw [frameVector,deviation_simple,hp]
theorem frame_covector_pivot (X : Fin (n-1) → G) (hp : ∀ i, simpleEntry (X i) i=1) (i : Fin (n-1)) :
    frameCovector X i (simpleRoot i).val.2=1 := by rw [frameCovector,deviation_simple,hp]

theorem frame_vector_zero (X : Fin (n-1) → G) (hU : ∀ i, X i ∈ Uplus n F)
    (i : Fin (n-1)) (a : Fin n) (ha : i.val<a.val) : frameVector X i a=0 :=
  deviation_zero_le _ (hU i) _ _ (by change i.val+1 ≤ a.val; omega)
theorem frame_covector_zero (X : Fin (n-1) → G) (hU : ∀ i, X i ∈ Uplus n F)
    (i : Fin (n-1)) (b : Fin n) (hb : b.val ≤ i.val) : frameCovector X i b=0 :=
  deviation_zero_le _ (hU i) _ _ hb

theorem frame_pairing_zero_le (X : Fin (n-1) → G) (hU : ∀ i, X i ∈ Uplus n F)
    (i j : Fin (n-1)) (hji : j.val ≤ i.val) : framePairing X i j=0 := by
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k.val ≤ i.val
  · rw [frame_covector_zero X hU i k hk,zero_mul]
  · rw [frame_vector_zero X hU j k (by omega),mul_zero]

theorem frame_deviation_product (X : Fin (n-1) → G)
    (hm : ∀ i a b d e, deviation (X i) a b*deviation (X i) d e=deviation (X i) a e*deviation (X i) d b)
    (hp : ∀ i, simpleEntry (X i) i=1) (i j : Fin (n-1)) (a b : Fin n) :
    (deviation (X i)*deviation (X j)) a b=
      frameVector X i a*framePairing X i j*frameCovector X j b := by
  classical
  rw [Matrix.mul_apply]
  calc
    _ = ∑ k : Fin n, (frameVector X i a*frameCovector X i k)*
        (frameVector X j k*frameCovector X j b) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [frame_factor X hm hp i a k,frame_factor X hm hp j k b]
    _ = _ := by
      simp only [framePairing,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem deviation_commute_of_commute (g h : G) (hc : g*h=h*g) :
    Commute (deviation g) (deviation h) := by
  have hv : Commute g.val h.val := congrArg Subtype.val hc
  exact (hv.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)

theorem commute_of_deviation_commute (g h : G) (hc : Commute (deviation g) (deviation h)) : g*h=h*g := by
  have he := (hc.add_left (Commute.one_left _)).add_right (Commute.one_right _)
  have hv : Commute g.val h.val := by simpa only [deviation,sub_add_cancel] using he
  exact Subtype.ext hv.eq

/-- The entire off-adjacent pairing table is forced by actual full-group
commutation relations and literal rank-one deviations. -/
theorem normalized_frame_pairing_far (hF : Fintype.card F=2) (hn : 4<n)
    (alpha : MulAut G) (hU : (Uplus n F).map alpha.toMonoidHom=Uplus n F)
    (hp : ∀ i, simpleEntry (alpha (root (simpleRoot i) 1)) i=1)
    (i j : Fin (n-1)) (hij : i.val+1<j.val) :
    framePairing (fun k => alpha (root (simpleRoot k) 1)) i j=0 := by
  let X : Fin (n-1) → G := fun k => alpha (root (simpleRoot k) 1)
  have hu : ∀ k, X k ∈ Uplus n F := by
    intro k; rw [← hU]; exact Subgroup.mem_map_of_mem _ (root_mem_Uplus _ _)
  have hm : ∀ k a b d e, deviation (X k) a b*deviation (X k) d e=deviation (X k) a e*deviation (X k) d b := by
    intro k; exact normalized_transvection_image_minors hF hn alpha hU _ _ _
  have hc : X i*X j=X j*X i := by
    simpa only [map_mul] using congrArg alpha (simple_roots_commute (F := F) i j (by omega) (by omega))
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) F =>
    M (simpleRoot i).val.1 (simpleRoot j).val.2) (deviation_commute_of_commute _ _ hc).eq
  rw [frame_deviation_product X hm hp,frame_deviation_product X hm hp,
    frame_pairing_zero_le X hu j i (by omega),mul_zero,zero_mul,
    frame_vector_pivot X hp,frame_covector_pivot X hp,one_mul,mul_one] at he
  exact he

/-- Adjacent source simple roots genuinely fail to commute. -/
theorem adjacent_simple_not_commute (i j : Fin (n-1)) (hij : j.val=i.val+1) :
    root (simpleRoot i) (1:F)*root (simpleRoot j) 1 ≠ root (simpleRoot j) 1*root (simpleRoot i) 1 := by
  intro hc
  let a := (simpleRoot i).val.1
  let b := (simpleRoot i).val.2
  let d := (simpleRoot j).val.2
  have he : (simpleRoot j).val.1=b := Fin.ext hij
  have hab : a<b := (simpleRoot i).property
  have hbd : b<d := he ▸ (simpleRoot j).property
  have hh := transvection_commutator_chain hab hbd (1:F) (1:F)
  have hcomm : SpecialLinearGroup.transvection (ne_of_lt hab) (1:F)*SpecialLinearGroup.transvection (ne_of_lt hbd) 1=
      SpecialLinearGroup.transvection (ne_of_lt hbd) 1*SpecialLinearGroup.transvection (ne_of_lt hab) 1 := by
    simpa only [root,he] using hc
  rw [mul_one, hcomm] at hh
  have hz : root (⟨(a,d),hab.trans hbd⟩ : PositiveIndex n) (1:F)=1 := by
    exact hh.symm.trans (by group)
  have hz0 : root (⟨(a,d),hab.trans hbd⟩ : PositiveIndex n) (0:F)=1 := by
    simp [root]
  exact one_ne_zero (root_injective _ (hz.trans hz0.symm))

/-- Adjacent pairings equal1 over F2, derived from genuine noncommutation. -/
theorem normalized_frame_pairing_adjacent (hF : Fintype.card F=2) (hn : 4<n)
    (alpha : MulAut G) (hU : (Uplus n F).map alpha.toMonoidHom=Uplus n F)
    (hp : ∀ i, simpleEntry (alpha (root (simpleRoot i) 1)) i=1)
    (i j : Fin (n-1)) (hij : j.val=i.val+1) :
    framePairing (fun k => alpha (root (simpleRoot k) 1)) i j=1 := by
  let X : Fin (n-1) → G := fun k => alpha (root (simpleRoot k) 1)
  have hu : ∀ k, X k ∈ Uplus n F := by
    intro k; rw [← hU]; exact Subgroup.mem_map_of_mem _ (root_mem_Uplus _ _)
  have hm : ∀ k a b d e, deviation (X k) a b*deviation (X k) d e=deviation (X k) a e*deviation (X k) d b := by
    intro k; exact normalized_transvection_image_minors hF hn alpha hU _ _ _
  apply (eq_zero_or_one hF _).resolve_left
  intro hz
  have hd : Commute (deviation (X i)) (deviation (X j)) := by
    ext a b
    rw [frame_deviation_product X hm hp,frame_deviation_product X hm hp,hz,
      frame_pairing_zero_le X hu j i (by omega),mul_zero,zero_mul,mul_zero,zero_mul]
  have hc := commute_of_deviation_commute _ _ hd
  apply adjacent_simple_not_commute (F := F) i j hij
  exact alpha.injective (by simpa only [map_mul] using hc)

end NikolovSegal.SLnF2Bare
