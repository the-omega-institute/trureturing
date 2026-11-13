/- GID: D5/S3/Combinatorics/Orthogonality/SevenBitCapacity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenBitCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenBitCapacity.class_property
   digest: Full original deleted-line independent-class capacity and saturation geometry. -/
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRow00
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows01
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows02
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows03
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows04
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows05
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows06
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows07
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows08
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows09
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows10
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows11
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows12
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows13
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows14
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows15
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows16
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows17
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows18
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows19
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows20
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows21
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows22
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows23
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows24
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows25
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows26
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows27
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows28
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows29
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows30
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows31
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.SevenBitClassRows32

/-! Minimum-vector partitioning covers every compatible class of the original
full deleted-line domain. Every row uses ordinary kernel reduction. No paused
n7 exclusions, coloring search, new axiom or source weakening is involved. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitCapacity
open SevenBitGeometry SevenBitClassDomains

private theorem all_rows (i : Fin 126) :
    CompatibleFamilyCheck.check good compatible 126 {minimum i} (candidates i) = true := by
  fin_cases i
  · exact SevenBitClassRow00.row_0
  · exact SevenBitClassRows01.row_1
  · exact SevenBitClassRows01.row_2
  · exact SevenBitClassRows01.row_3
  · exact SevenBitClassRows01.row_4
  · exact SevenBitClassRows02.row_5
  · exact SevenBitClassRows02.row_6
  · exact SevenBitClassRows02.row_7
  · exact SevenBitClassRows02.row_8
  · exact SevenBitClassRows03.row_9
  · exact SevenBitClassRows03.row_10
  · exact SevenBitClassRows03.row_11
  · exact SevenBitClassRows03.row_12
  · exact SevenBitClassRows04.row_13
  · exact SevenBitClassRows04.row_14
  · exact SevenBitClassRows04.row_15
  · exact SevenBitClassRows04.row_16
  · exact SevenBitClassRows05.row_17
  · exact SevenBitClassRows05.row_18
  · exact SevenBitClassRows05.row_19
  · exact SevenBitClassRows05.row_20
  · exact SevenBitClassRows06.row_21
  · exact SevenBitClassRows06.row_22
  · exact SevenBitClassRows06.row_23
  · exact SevenBitClassRows06.row_24
  · exact SevenBitClassRows07.row_25
  · exact SevenBitClassRows07.row_26
  · exact SevenBitClassRows07.row_27
  · exact SevenBitClassRows07.row_28
  · exact SevenBitClassRows08.row_29
  · exact SevenBitClassRows08.row_30
  · exact SevenBitClassRows08.row_31
  · exact SevenBitClassRows08.row_32
  · exact SevenBitClassRows09.row_33
  · exact SevenBitClassRows09.row_34
  · exact SevenBitClassRows09.row_35
  · exact SevenBitClassRows09.row_36
  · exact SevenBitClassRows10.row_37
  · exact SevenBitClassRows10.row_38
  · exact SevenBitClassRows10.row_39
  · exact SevenBitClassRows10.row_40
  · exact SevenBitClassRows11.row_41
  · exact SevenBitClassRows11.row_42
  · exact SevenBitClassRows11.row_43
  · exact SevenBitClassRows11.row_44
  · exact SevenBitClassRows12.row_45
  · exact SevenBitClassRows12.row_46
  · exact SevenBitClassRows12.row_47
  · exact SevenBitClassRows12.row_48
  · exact SevenBitClassRows13.row_49
  · exact SevenBitClassRows13.row_50
  · exact SevenBitClassRows13.row_51
  · exact SevenBitClassRows13.row_52
  · exact SevenBitClassRows14.row_53
  · exact SevenBitClassRows14.row_54
  · exact SevenBitClassRows14.row_55
  · exact SevenBitClassRows14.row_56
  · exact SevenBitClassRows15.row_57
  · exact SevenBitClassRows15.row_58
  · exact SevenBitClassRows15.row_59
  · exact SevenBitClassRows15.row_60
  · exact SevenBitClassRows16.row_61
  · exact SevenBitClassRows16.row_62
  · exact SevenBitClassRows16.row_63
  · exact SevenBitClassRows16.row_64
  · exact SevenBitClassRows17.row_65
  · exact SevenBitClassRows17.row_66
  · exact SevenBitClassRows17.row_67
  · exact SevenBitClassRows17.row_68
  · exact SevenBitClassRows18.row_69
  · exact SevenBitClassRows18.row_70
  · exact SevenBitClassRows18.row_71
  · exact SevenBitClassRows18.row_72
  · exact SevenBitClassRows19.row_73
  · exact SevenBitClassRows19.row_74
  · exact SevenBitClassRows19.row_75
  · exact SevenBitClassRows19.row_76
  · exact SevenBitClassRows20.row_77
  · exact SevenBitClassRows20.row_78
  · exact SevenBitClassRows20.row_79
  · exact SevenBitClassRows20.row_80
  · exact SevenBitClassRows21.row_81
  · exact SevenBitClassRows21.row_82
  · exact SevenBitClassRows21.row_83
  · exact SevenBitClassRows21.row_84
  · exact SevenBitClassRows22.row_85
  · exact SevenBitClassRows22.row_86
  · exact SevenBitClassRows22.row_87
  · exact SevenBitClassRows22.row_88
  · exact SevenBitClassRows23.row_89
  · exact SevenBitClassRows23.row_90
  · exact SevenBitClassRows23.row_91
  · exact SevenBitClassRows23.row_92
  · exact SevenBitClassRows24.row_93
  · exact SevenBitClassRows24.row_94
  · exact SevenBitClassRows24.row_95
  · exact SevenBitClassRows24.row_96
  · exact SevenBitClassRows25.row_97
  · exact SevenBitClassRows25.row_98
  · exact SevenBitClassRows25.row_99
  · exact SevenBitClassRows25.row_100
  · exact SevenBitClassRows26.row_101
  · exact SevenBitClassRows26.row_102
  · exact SevenBitClassRows26.row_103
  · exact SevenBitClassRows26.row_104
  · exact SevenBitClassRows27.row_105
  · exact SevenBitClassRows27.row_106
  · exact SevenBitClassRows27.row_107
  · exact SevenBitClassRows27.row_108
  · exact SevenBitClassRows28.row_109
  · exact SevenBitClassRows28.row_110
  · exact SevenBitClassRows28.row_111
  · exact SevenBitClassRows28.row_112
  · exact SevenBitClassRows29.row_113
  · exact SevenBitClassRows29.row_114
  · exact SevenBitClassRows29.row_115
  · exact SevenBitClassRows29.row_116
  · exact SevenBitClassRows30.row_117
  · exact SevenBitClassRows30.row_118
  · exact SevenBitClassRows30.row_119
  · exact SevenBitClassRows30.row_120
  · exact SevenBitClassRows31.row_121
  · exact SevenBitClassRows31.row_122
  · exact SevenBitClassRows31.row_123
  · exact SevenBitClassRows31.row_124
  · exact SevenBitClassRows32.row_125

/-- Every actual compatible class avoiding precisely0 and127 has the original
size bound and all saturated quadratic/Lagrangian data. -/
theorem class_property (S : Finset Vector)
    (hdom : ∀ v ∈ S, v ≠ 0 ∧ v ≠ 127)
    (hpair : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → dot u v ≠ 0) : ClassProperty S := by
  classical
  by_cases hn : S.Nonempty
  · let a := S.min' hn
    have ha : a ∈ S := Finset.min'_mem S hn
    have had := hdom a ha
    have hat : a.val < 128 := a.isLt
    have hap : 0 < a.val := by
      by_contra h
      have hz : a = 0 := Fin.ext (by omega)
      exact had.1 hz
    let i : Fin 126 := ⟨a.val-1,by
      have hz : a.val ≠ 127 := by
        intro h
        exact had.2 (Fin.ext h)
      omega⟩
    have hia : minimum i = a := Fin.ext (by simp [minimum,i]; omega)
    have hp : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → compatible u v = true := by
      intro u hu v hv huv
      have hn := hpair u hu v hv huv
      have hb : dot u v < 2 := Nat.mod_lt _ (by decide)
      have he : dot u v = 1 := by omega
      simp [compatible,he]
    have hs : ∀ v ∈ S.erase a, v ∈ candidates i := by
      intro v hv
      have hv' := Finset.mem_erase.mp hv
      have hd : v ∈ deleted := by simp [deleted,hdom v hv'.2]
      have hle : a ≤ v := Finset.min'_le S v hv'.2
      have hlt : a < v := lt_of_le_of_ne hle hv'.1.symm
      simp only [candidates,List.mem_filter,Bool.and_eq_true_iff,decide_eq_true_eq]
      exact ⟨hd,hia.symm ▸ hlt,hia.symm ▸ hp a ha v hv'.2 hv'.1.symm⟩
    have hlen : (candidates i).length ≤ 126 :=
      (List.length_filter_le _ _).trans (by decide +kernel : deleted.length ≤ 126)
    have hpair' : ∀ u ∈ S.erase a, ∀ v ∈ S.erase a,
        u ≠ v → compatible u v = true := by
      intro u hu v hv huv
      exact hp u (Finset.mem_of_mem_erase hu) v (Finset.mem_of_mem_erase hv) huv
    have hh := CompatibleFamilyCheck.sound good compatible 126 {minimum i}
      (candidates i) hlen (S.erase a) hs hpair' (all_rows i)
    have he : ({minimum i} : Finset Vector) ∪ S.erase a = S := by
      rw [hia,Finset.singleton_union,Finset.insert_erase ha]
    simpa [good,he] using hh
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he,ClassProperty]


/-- The full original127-line domain: every independent class has at most
 eight points, and every eight-point class is the characteristic point plus
 the odd representatives of a full original Lagrangian. -/
theorem full_class_property (S : Finset Vector)
    (hdom : ∀ v ∈ S, v ≠ 0)
    (hpair : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → dot u v ≠ 0) :
    S.card ≤ 8 ∧ (S.card = 8 → 127 ∈ S ∧
      LagrangianData (oddPoints (S.erase 127)) ∧
      S = insert 127 ((oddPoints (S.erase 127)).image oddPoint)) := by
  classical
  have hz : ∀ v : Vector, dot 127 v = dot v v := by decide +kernel
  have hinv : Function.Involutive oddPoint := by
    change ∀ v : Vector, oddPoint (oddPoint v) = v
    decide +kernel
  have he : ClassProperty (S.erase 127) := class_property _
    (fun v hv => ⟨hdom v (Finset.mem_of_mem_erase hv),(Finset.mem_erase.mp hv).1⟩)
    (fun u hu v hv huv => hpair u (Finset.mem_of_mem_erase hu)
      v (Finset.mem_of_mem_erase hv) huv)
  have hb := he.1
  have hc : S.card ≤ 8 := by
    by_cases ha : (127 : Vector) ∈ S
    · have h := Finset.card_erase_add_one ha
      omega
    · have h := Finset.erase_eq_of_notMem ha
      have hh := he.1
      rw [h] at hh
      omega
  refine ⟨hc,?_⟩
  intro h8
  have ha : (127 : Vector) ∈ S := by
    by_contra hn
    have hh := he.1
    rw [Finset.erase_eq_of_notMem hn] at hh
    omega
  have h7 : (S.erase 127).card = 7 := by
    have h := Finset.card_erase_add_one ha
    omega
  have ho (v : Vector) (hv : v ∈ S.erase 127) : ¬ even v := by
    have hne : (127 : Vector) ≠ v := (Finset.mem_erase.mp hv).1.symm
    have hp := hpair 127 ha v (Finset.mem_of_mem_erase hv) hne
    simpa only [hz,even] using hp
  have hem : evenPart (S.erase 127) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hh := Finset.mem_filter.mp hv
    exact ho v hh.1 hh.2
  have hlag : LagrangianData (oddPoints (S.erase 127)) := by
    rcases he.2 h7 with ⟨h,_⟩ | h | ⟨_,h⟩
    · simp [hem] at h
    · simp [hem] at h
    · exact h
  have him : (oddPoints (S.erase 127)).image oddPoint = S.erase 127 := by
    have hf : (S.erase 127).filter (fun v => ¬ even v) = S.erase 127 :=
      Finset.filter_eq_self.mpr ho
    simp only [oddPoints,hf,Finset.image_image]
    have hinv' (x : Vector) : oddPoint (oddPoint x) = x := hinv x
    simp only [Function.comp_def,hinv']
    exact Finset.image_id
  exact ⟨ha,hlag,by rw [him,Finset.insert_erase ha]⟩


/-- The entire actual coordinate submodule of a supplied full Lagrangian.
The carrier includes zero and every supplied nonzero point. -/
def actualLagrangian (L : Finset Vector) (h : LagrangianData L) :
    Submodule (ZMod 2) Coordinates where
  carrier := bits '' ((insert 0 L : Finset Vector) : Set Vector)
  zero_mem' := ⟨0,by simp,bits_zero⟩
  add_mem' := by
    rintro _ _ ⟨u,hu,rfl⟩ ⟨v,hv,rfl⟩
    exact ⟨add u v,h.2.2.2.1 u hu v hv,bits_add u v⟩
  smul_mem' := by
    intro c v hv
    have hc : c = 0 ∨ c = 1 := by
      have hall : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
      exact hall c
    rcases hc with rfl | rfl
    · simpa only [zero_smul] using
        (show (0 : Coordinates) ∈ bits '' ((insert 0 L : Finset Vector) : Set Vector) from
          ⟨0,by simp,bits_zero⟩)
    · simpa only [one_smul] using hv

/-- Exact cardinality and full coordinate orthogonality, with no selected
basis or proper-subspace substitution. -/
theorem actual_lagrangian_geometry (L : Finset Vector) (h : LagrangianData L) :
    Module.finrank (ZMod 2) (actualLagrangian L h) = 3 ∧
    ∀ u ∈ actualLagrangian L h, ∀ v ∈ actualLagrangian L h,
      dotProduct u v = 0 := by
  classical
  let f : {v : Vector // v ∈ insert 0 L} → actualLagrangian L h :=
    fun v => ⟨bits v,⟨v,v.property,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      exact Subtype.ext (bits_bijective.1 (congrArg Subtype.val huv))
    · rintro ⟨v,hv⟩
      obtain ⟨u,hu,huv⟩ := hv
      exact ⟨⟨u,hu⟩,Subtype.ext huv⟩
  have hz : (0 : Vector) ∉ L := by
    intro hz
    exact (Finset.mem_filter.mp (h.1 hz)).2.1 rfl
  have hn : Nat.card (actualLagrangian L h) = 8 := by
    calc
      _ = Nat.card {v : Vector // v ∈ insert 0 L} :=
        (Nat.card_congr (Equiv.ofBijective f hf)).symm
      _ = 8 := by
        rw [Nat.card_eq_fintype_card,Fintype.card_coe,Finset.card_insert_of_notMem hz,h.2.1]
  have hp : 2 ^ Module.finrank (ZMod 2) (actualLagrangian L h) = 2 ^ 3 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_eq_fintype_card,ZMod.card] at hn
    exact hn
  refine ⟨Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) hp,?_⟩
  rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩
  apply (bits_dot u v).mpr
  rcases Finset.mem_insert.mp hu with rfl | hu
  · simp [dot]
  rcases Finset.mem_insert.mp hv with rfl | hv
  · simp [dot]
  exact h.2.2.1 u hu v hv

/-- Every original eight-point independent class recovers an actual full
three-dimensional totally isotropic coordinate submodule. -/
theorem full_saturated_actual (S : Finset Vector)
    (hdom : ∀ v ∈ S, v ≠ 0)
    (hpair : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → dot u v ≠ 0)
    (h8 : S.card = 8) : ∃ L : Submodule (ZMod 2) Coordinates,
      Module.finrank (ZMod 2) L = 3 ∧
      (∀ u ∈ L, ∀ v ∈ L, dotProduct u v = 0) ∧
      (L : Set Coordinates) = bits '' ((insert 0 (oddPoints (S.erase 127)) : Finset Vector) : Set Vector) ∧
      S = insert 127 ((oddPoints (S.erase 127)).image oddPoint) := by
  obtain ⟨_,hlag,heq⟩ := (full_class_property S hdom hpair).2 h8
  have hg := actual_lagrangian_geometry _ hlag
  exact ⟨actualLagrangian _ hlag,hg.1,hg.2,rfl,heq⟩

#print axioms class_property
#print axioms full_saturated_actual
#print axioms full_class_property
end D5.S3.Combinatorics.Orthogonality.SevenBitCapacity
