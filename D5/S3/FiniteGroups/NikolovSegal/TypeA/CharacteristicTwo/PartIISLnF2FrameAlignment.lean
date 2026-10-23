/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2FrameAlignment
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2FrameAlignment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo.PartIISLnF2RankOneFrame
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace NikolovSegal.SLnF2Bare
open Matrix NikolovSegal.SLnRootAction NikolovSegal.SLnFullGroup
open NikolovSegal.SLnNormalizer NikolovSegal.SLnF2Residual
universe u
variable {F : Type u} [Field F] [Fintype F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F

noncomputable def frameLast (X : Fin (n-1) → G) (hn : 4<n) (a : Fin n) : F :=
  (1 : Matrix (Fin n) (Fin n) F) a (last hn) -
    ∑ i : Fin (n-1), if hi : i.val+1<n-1 then
      frameCovector X i (last hn)*frameVector X ⟨i.val+1,hi⟩ a else 0

noncomputable def frameMatrix (X : Fin (n-1) → G) (hn : 4<n) : Matrix (Fin n) (Fin n) F :=
  fun a b => if hb : b.val<n-1 then frameVector X ⟨b.val,hb⟩ a else frameLast X hn a

/-- Explicit completion of the last column; all earlier columns are the
rank-one image vectors. Its diagonal and triangularity are genuine. -/
theorem frameMatrix_upper_diag (X : Fin (n-1) → G) (hn : 4<n)
    (hU : ∀ i, X i ∈ Uplus n F) (hp : ∀ i, simpleEntry (X i) i=1) :
    (∀ a b, b.val<a.val → frameMatrix X hn a b=0) ∧
    ∀ a, frameMatrix X hn a a=1 := by
  classical
  have hlast : ∀ i : Fin (n-1), ∀ hi : i.val+1<n-1,
      frameVector X ⟨i.val+1,hi⟩ (last hn)=0 := by
    intro i hi
    apply frame_vector_zero X hU
    change i.val+1<n-1
    exact hi
  constructor
  · intro a b hab
    have hb : b.val<n-1 := by have ha:=a.isLt; omega
    rw [frameMatrix,dif_pos hb]
    exact frame_vector_zero X hU _ _ hab
  · intro a
    by_cases ha : a.val<n-1
    · rw [frameMatrix,dif_pos ha]
      exact frame_vector_pivot X hp ⟨a.val,ha⟩
    · have he : a=last hn := Fin.ext (by have hb:=a.isLt; dsimp [last]; omega)
      subst a
      simp only [frameMatrix,dif_neg (by omega : ¬ (last hn).val<n-1),frameLast,
        Matrix.one_apply_eq]
      have hz : (∑ i : Fin (n-1), if hi : i.val+1<n-1 then
          frameCovector X i (last hn)*frameVector X ⟨i.val+1,hi⟩ (last hn) else 0)=0 := by
        apply Finset.sum_eq_zero
        intro i _
        split_ifs with hi
        · rw [hlast i hi,mul_zero]
        · rfl
      rw [hz,sub_zero]

/-- The last-column correction solves the whole triangular covector system,
not a target-dependent or assumed basis choice. -/
theorem frameLast_pairing (X : Fin (n-1) → G) (hn : 4<n)
    (hp : ∀ i, simpleEntry (X i) i=1)
    (hpair : ∀ i j, framePairing X i j=if j.val=i.val+1 then 1 else 0)
    (j : Fin (n-1)) :
    (∑ k : Fin n, frameCovector X j k*frameLast X hn k)=
      if (last hn).val=j.val+1 then 1 else 0 := by
  classical
  simp only [frameLast,mul_sub,Finset.sum_sub_distrib]
  have hone : (∑ k : Fin n, frameCovector X j k*(1 : Matrix (Fin n) (Fin n) F) k (last hn))=
      frameCovector X j (last hn) := by simp [Matrix.one_apply]
  rw [hone]
  have hsum : (∑ k : Fin n, frameCovector X j k *
      ∑ i : Fin (n-1), if hi : i.val+1<n-1 then
        frameCovector X i (last hn)*frameVector X ⟨i.val+1,hi⟩ k else 0)=
      ∑ i : Fin (n-1), if hi : i.val+1<n-1 then
        frameCovector X i (last hn)*framePairing X j ⟨i.val+1,hi⟩ else 0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val+1<n-1
    · simp only [dif_pos hi,framePairing,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    · simp only [dif_neg hi,mul_zero,Finset.sum_const_zero]
  rw [hsum]
  have hcollapse : (∑ i : Fin (n-1), if hi : i.val+1<n-1 then
      frameCovector X i (last hn)*framePairing X j ⟨i.val+1,hi⟩ else 0)=
      if hj : j.val+1<n-1 then frameCovector X j (last hn) else 0 := by
    rw [Finset.sum_eq_single j]
    · split_ifs with hj
      · rw [hpair,if_pos rfl,mul_one]
      · rfl
    · intro i _ hij
      split_ifs with hi
      · rw [hpair,if_neg (by intro he; apply hij; apply Fin.ext; dsimp at he; omega),mul_zero]
      · rfl
    · simp
  rw [hcollapse]
  by_cases hj : j.val+1<n-1
  · rw [dif_pos hj,sub_self,if_neg (by change ¬ (n-1=j.val+1); omega)]
  · have he : (simpleRoot j).val.2=last hn := Fin.ext (by
      have hb:=j.isLt; dsimp [simpleRoot,last]; omega)
    have hc := frame_covector_pivot X hp j
    rw [he] at hc
    rw [dif_neg hj,sub_zero,hc,if_pos (by have hb:=j.isLt; change n-1=j.val+1; omega)]

theorem frameMatrix_pairing (X : Fin (n-1) → G) (hn : 4<n)
    (hp : ∀ i, simpleEntry (X i) i=1)
    (hpair : ∀ i j, framePairing X i j=if j.val=i.val+1 then 1 else 0)
    (i : Fin (n-1)) (b : Fin n) :
    (∑ k : Fin n, frameCovector X i k*frameMatrix X hn k b)=
      if b=(simpleRoot i).val.2 then 1 else 0 := by
  classical
  by_cases hb : b.val<n-1
  · simp only [frameMatrix,dif_pos hb]
    change framePairing X i ⟨b.val,hb⟩= _
    rw [hpair]
    congr 1
    exact propext (by simpa only [simpleRoot] using (Fin.ext_iff (a := b) (b := (simpleRoot i).val.2)).symm)
  · have he : b=last hn := Fin.ext (by have hb':=b.isLt; dsimp [last]; omega)
    subst b
    simp only [frameMatrix,dif_neg hb]
    rw [frameLast_pairing X hn hp hpair]
    congr 1
    exact propext (by simpa only [simpleRoot] using (Fin.ext_iff (a := last hn) (b := (simpleRoot i).val.2)).symm)

noncomputable def frameSL (X : Fin (n-1) → G) (hn : 4<n)
    (hU : ∀ i, X i ∈ Uplus n F) (hp : ∀ i, simpleEntry (X i) i=1) : G :=
  ⟨frameMatrix X hn,by
    have h := frameMatrix_upper_diag X hn hU hp
    rw [Matrix.det_of_isUpperTriangular (show (frameMatrix X hn).IsUpperTriangular from h.1)]
    simp only [h.2,Finset.prod_const_one]⟩

theorem frameSL_mem_Uplus (X : Fin (n-1) → G) (hn : 4<n)
    (hU : ∀ i, X i ∈ Uplus n F) (hp : ∀ i, simpleEntry (X i) i=1) :
    frameSL X hn hU hp ∈ Uplus n F := frameMatrix_upper_diag X hn hU hp

/-- One explicit actual determinant-one U matrix simultaneously conjugates
all simple roots to the given rank-one frame. -/
theorem frameSL_conjugates (X : Fin (n-1) → G) (hn : 4<n)
    (hU : ∀ i, X i ∈ Uplus n F) (hp : ∀ i, simpleEntry (X i) i=1)
    (hm : ∀ i a b d e, deviation (X i) a b*deviation (X i) d e=deviation (X i) a e*deviation (X i) d b)
    (hpair : ∀ i j, framePairing X i j=if j.val=i.val+1 then 1 else 0)
    (i : Fin (n-1)) :
    (MulAut.conj (frameSL X hn hU hp)) (root (simpleRoot i) 1)=X i := by
  let C := frameSL X hn hU hp
  have hcol : ∀ a, C.val a (simpleRoot i).val.1=frameVector X i a := by
    intro a
    change frameMatrix X hn a (simpleRoot i).val.1= _
    rw [frameMatrix,dif_pos (by exact i.isLt)]
    congr 1
  have hmul : X i*C=C*root (simpleRoot i) 1 := by
    apply Subtype.ext
    have hx : (X i).val=1+deviation (X i) := by dsimp [deviation]; abel
    change (X i).val*C.val=C.val*(1+Matrix.single (simpleRoot i).val.1 (simpleRoot i).val.2 1)
    rw [hx,Matrix.add_mul,Matrix.mul_add,Matrix.one_mul,Matrix.mul_one]
    congr 1
    ext a b
    rw [Matrix.mul_apply,Matrix.mul_apply]
    have he : (∑ k : Fin n, deviation (X i) a k*C.val k b)=
        frameVector X i a*(if b=(simpleRoot i).val.2 then 1 else 0) := by
      calc
        _ = frameVector X i a*(∑ k : Fin n,frameCovector X i k*C.val k b) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [frame_factor X hm hp i a k]
          ring
        _ = _ := by rw [show (∑ k : Fin n,frameCovector X i k*C.val k b)=
            if b=(simpleRoot i).val.2 then 1 else 0 from frameMatrix_pairing X hn hp hpair i b]
    rw [he]
    simp only [Matrix.single_apply]
    rw [Finset.sum_eq_single (simpleRoot i).val.1]
    · rw [hcol]
      by_cases hb : b=(simpleRoot i).val.2
      · simp [hb]
      · simp [hb,Ne.symm hb]
    · intro k _ hk
      simp [hk,hk.symm]
    · simp
  change C*root (simpleRoot i) 1*C⁻¹=X i
  rw [← hmul]
  simp [mul_assoc]

end NikolovSegal.SLnF2Bare
