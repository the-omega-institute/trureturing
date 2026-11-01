/- GID: D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Equivalence
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Equivalence
   mirror-E: none(waiver:consumed-packet-equivalence)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical packet canonicalization preserves both endpoint readouts. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Certificate

/-! Internal orders are eliminated by physical finite sets, preserving both masses. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open SourceWidth
open private blocksWord blocksWord_flatMap insertAt split_packets
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private strip_append_iff last_nonpositive ear_not_at_end
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Transport
open private packetChecks withEar strip_iff_packetChecks normalize_blocks withEar_split
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private orderedPackets finiteChecks finiteEarChecks DataCertificate DataCertificate.mk
  finiteChecks_equiv finiteEarChecks_equiv
  DataCertificate.packets DataCertificate.negativeOrder DataCertificate.earSlot
  DataCertificate.positiveLabels DataCertificate.partition
  DataCertificate.oldEndpoints DataCertificate.newEndpoints
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Certificate

private def finitePackets (bs : List (List ℕ × ℕ)) : List (Finset ℕ × ℕ) :=
  bs.map (fun b => (b.1.toFinset,b.2))

private theorem finite_packets_perm (bs : List (List ℕ × ℕ))
    (hnd : ∀ b ∈ bs, b.1.Nodup) :
    (blocksWord (orderedPackets (finitePackets bs))).Perm (blocksWord bs) := by
  induction bs with
  | nil => exact List.Perm.refl _
  | cons b bs ih =>
    rcases b with ⟨P,n⟩
    have hP := hnd (P,n) (by simp)
    have hs : ∀ b ∈ bs, b.1.Nodup := fun b hb => hnd b (by simp [hb])
    change (P.toFinset.toList ++ n :: blocksWord (orderedPackets (finitePackets bs))).Perm
      (P ++ n :: blocksWord bs)
    exact (List.toFinset_toList hP).append (List.Perm.cons n (ih hs))

private theorem finite_packet_checks (f : ℕ → ℤ) (C h : ℤ)
    (bs : List (List ℕ × ℕ)) (hnd : ∀ b ∈ bs, b.1.Nodup) :
    packetChecks f C h (orderedPackets (finitePackets bs)) ↔ packetChecks f C h bs := by
  induction bs generalizing h with
  | nil => rfl
  | cons b bs ih =>
    rcases b with ⟨P,n⟩
    have hs : ∀ b ∈ bs, b.1.Nodup := fun b hb => hnd b (by simp [hb])
    have hmass := ((List.toFinset_toList (hnd (P,n) (by simp))).map f).sum_eq
    change (0 ≤ h + (P.toFinset.toList.map f).sum + f n ∧
      h + (P.toFinset.toList.map f).sum ≤ C ∧
      packetChecks f C (h + (P.toFinset.toList.map f).sum + f n)
        (orderedPackets (finitePackets bs))) ↔ _
    rw [hmass]
    exact and_congr Iff.rfl (and_congr Iff.rfl (ih _ hs))

private theorem finite_ear_checks (f : ℕ → ℤ) (C h : ℤ) (ear e : ℕ)
    (bs : List (List ℕ × ℕ)) (hnd : ∀ b ∈ bs, b.1.Nodup) :
    packetChecks f C h (withEar ear e (orderedPackets (finitePackets bs))) ↔
      packetChecks f C h (withEar ear e bs) := by
  induction bs generalizing h e with
  | nil => rfl
  | cons b bs ih =>
    rcases b with ⟨P,n⟩
    have hs : ∀ b ∈ bs, b.1.Nodup := fun b hb => hnd b (by simp [hb])
    have hmass := ((List.toFinset_toList (hnd (P,n) (by simp))).map f).sum_eq
    cases e with
    | zero =>
      change (0 ≤ h + ((P.toFinset.toList ++ [ear]).map f).sum + f n ∧
        h + ((P.toFinset.toList ++ [ear]).map f).sum ≤ C ∧
        packetChecks f C (h + ((P.toFinset.toList ++ [ear]).map f).sum + f n)
          (orderedPackets (finitePackets bs))) ↔ _
      simp only [withEar,packetChecks,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,hmass]
      exact and_congr Iff.rfl (and_congr Iff.rfl (finite_packet_checks f C _ bs hs))
    | succ e =>
      change (0 ≤ h + (P.toFinset.toList.map f).sum + f n ∧
        h + (P.toFinset.toList.map f).sum ≤ C ∧
        packetChecks f C (h + (P.toFinset.toList.map f).sum + f n)
          (withEar ear e (orderedPackets (finitePackets bs)))) ↔ _
      rw [hmass]
      exact and_congr Iff.rfl (and_congr Iff.rfl (ih _ e hs))

private theorem withEar_positive (f : ℕ → ℤ) (ear e : ℕ)
    (bs : List (List ℕ × ℕ)) (he : 0 ≤ f ear)
    (hp : ∀ b ∈ bs, ∀ i ∈ b.1, 0 ≤ f i) :
    ∀ b ∈ withEar ear e bs, ∀ i ∈ b.1, 0 ≤ f i := by
  induction bs generalizing e with
  | nil => simp [withEar]
  | cons b bs ih =>
    rcases b with ⟨P,n⟩
    have hs : ∀ b ∈ bs, ∀ i ∈ b.1, 0 ≤ f i := fun b hb => hp b (by simp [hb])
    cases e with
    | zero =>
      intro b hb i hi
      rcases List.mem_cons.mp hb with hb | hb
      · subst b
        rcases List.mem_append.mp hi with hi | hi
        · exact hp (P,n) (by simp) i hi
        · have h := List.mem_singleton.mp hi
          simpa only [h] using he
      · exact hs b hb i hi
    | succ e =>
      intro b hb i hi
      rcases List.mem_cons.mp hb with hb | hb
      · subst b; exact hp (P,n) (by simp) i hi
      · exact ih e hs b hb i hi

private theorem withEar_negatives (ear e : ℕ) (bs : List (List ℕ × ℕ)) :
    (withEar ear e bs).map Prod.snd = bs.map Prod.snd := by
  induction bs generalizing e with
  | nil => simp [withEar]
  | cons b bs ih => cases e <;> simp [withEar,ih]

private theorem physical_packet_equivalence (k : ℕ) (f g : ℕ → ℤ) (C D E : ℤ)
    (ng : List ℕ) (mass mass' : Finset ℕ → ℤ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 < E) (hear : g k = E)
    (hng : ng.Nodup) (hnglen : ng.length = 4) (hngrange : ∀ n ∈ ng, n < k)
    (hsign : ∀ i < k, if i ∈ ng then f i < 0 ∧ g i < 0 else 0 < f i ∧ 0 < g i)
    (hfzero : ((List.range k).map f).sum = 0)
    (hgzero : ((List.range k).map g).sum = -E)
    (hmass : ∀ P : Finset ℕ, (∀ i ∈ P, i < k ∧ i ∉ ng) → mass P = ∑ i ∈ P, f i)
    (hmass' : ∀ P : Finset ℕ, (∀ i ∈ P, i < k ∧ i ∉ ng) → mass' P = ∑ i ∈ P, g i) :
    (∃ l : List ℕ, l.Perm (List.range k) ∧ InStrip f C 0 l ∧
      ∃ j : ℕ, j ≤ k ∧ InStrip g D 0 (insertAt k l j)) ↔
      Nonempty (DataCertificate k f g C D E ng mass mass') := by
  constructor
  · rintro ⟨l,hperm,hold,j,hj,hnew⟩
    have hlen : l.length = k := by simpa using hperm.length_eq
    have hmem (i : ℕ) (hi : i ∈ l) : i < k := List.mem_range.mp (hperm.mem_iff.mp hi)
    have hz : (l.map f).sum = 0 := (hperm.map f).sum_eq.trans hfzero
    have hz' : (l.map g).sum = -E := (hperm.map g).sum_eq.trans hgzero
    have hlast : ∀ pre n, l = pre ++ [n] → n ∈ ng := by
      intro pre n he
      have hnmem : n ∈ l := by rw [he]; simp
      have hs := hsign n (hmem n hnmem)
      have hnle := last_nonpositive f C pre n (by simpa [← he] using hold)
        (by simpa [← he] using hz)
      by_contra hn
      rw [if_neg hn] at hs
      omega
    obtain ⟨bs,hword,hpos,hnegs⟩ := split_packets (fun i => i ∈ ng) l hlast
    have hfilter : (l.filter (fun i => decide (i ∈ ng))).Perm ng := by
      apply (hperm.filter (fun i => decide (i ∈ ng))).trans
      apply List.perm_of_nodup_nodup_toFinset_eq ((List.nodup_range (n := k)).filter _) hng
      ext i
      simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq,List.mem_range]
      exact ⟨And.right,fun hi => ⟨hngrange i hi,hi⟩⟩
    have hnegative : (bs.map Prod.snd).Perm ng := by rw [hnegs]; exact hfilter
    have hbslen : bs.length = 4 := by simpa [hnglen] using hnegative.length_eq
    have hndall : ∀ b ∈ bs, b.1.Nodup := by
      have hnword : (blocksWord bs).Nodup := by
        rw [hword]
        exact hperm.nodup_iff.mpr (List.nodup_range (n := k))
      rw [blocksWord_flatMap] at hnword
      have hnblocks := (List.nodup_flatMap.mp hnword).1
      intro b hb
      exact (List.nodup_append.mp (hnblocks b hb)).1
    have hlabels : ∀ b ∈ bs, ∀ i ∈ b.1, i < k ∧ i ∉ ng := by
      intro b hb i hi
      have hil : i ∈ l := by
        rw [← hword,blocksWord_flatMap]
        apply List.mem_flatMap.mpr
        exact ⟨b,hb,by simp [hi]⟩
      exact ⟨hmem i hil,hpos b hb i hi⟩
    have hpold : ∀ b ∈ bs, ∀ i ∈ b.1, 0 ≤ f i := by
      intro b hb i hi
      have hs := hsign i (hlabels b hb i hi).1
      rw [if_neg (hlabels b hb i hi).2] at hs
      exact hs.1.le
    have hpnew : ∀ b ∈ bs, ∀ i ∈ b.1, 0 ≤ g i := by
      intro b hb i hi
      have hs := hsign i (hlabels b hb i hi).1
      rw [if_neg (hlabels b hb i hi).2] at hs
      exact hs.2.le
    have hnegf : ∀ b ∈ bs, f b.2 ≤ 0 := by
      intro b hb
      have hn : b.2 ∈ ng := hnegative.mem_iff.mp (List.mem_map.mpr ⟨b,hb,rfl⟩)
      have hs := hsign b.2 (hngrange b.2 hn)
      rw [if_pos hn] at hs
      exact hs.1.le
    have hnegg : ∀ b ∈ bs, g b.2 ≤ 0 := by
      intro b hb
      have hn : b.2 ∈ ng := hnegative.mem_iff.mp (List.mem_map.mpr ⟨b,hb,rfl⟩)
      have hs := hsign b.2 (hngrange b.2 hn)
      rw [if_pos hn] at hs
      exact hs.2.le
    have hjlt : j < l.length := by
      by_contra hh
      have he : j = l.length := by omega
      rw [he] at hnew
      apply ear_not_at_end g D l k E hE hz'
      simpa [insertAt] using hnew
    obtain ⟨e,he,hmarked⟩ := normalize_blocks g D 0 k bs j (by simpa [hword] using hjlt)
      (by rw [hear]; exact hE.le) hpnew (by simpa [hword] using hnew)
    have hmarkedpos := withEar_positive g k e bs (by rw [hear]; exact hE.le) hpnew
    have hmarkedneg : ∀ b ∈ withEar k e bs, g b.2 ≤ 0 := by
      intro b hb
      have hn : b.2 ∈ bs.map Prod.snd := by
        rw [← withEar_negatives k e bs]
        exact List.mem_map.mpr ⟨b,hb,rfl⟩
      obtain ⟨b',hb',heq⟩ := List.mem_map.mp hn
      simpa [heq] using hnegg b' hb'
    have holdchecks := (strip_iff_packetChecks f C 0 bs ⟨by omega,hC⟩ hpold hnegf).mp
      (by simpa [hword] using hold)
    have hnewchecks := (strip_iff_packetChecks g D 0 (withEar k e bs) ⟨by omega,hD⟩
      hmarkedpos hmarkedneg).mp hmarked
    have hlabels' : ∀ b ∈ finitePackets bs, ∀ i ∈ b.1, i < k ∧ i ∉ ng := by
      intro b hb i hi
      obtain ⟨b',hb',rfl⟩ := List.mem_map.mp hb
      exact hlabels b' hb' i (List.mem_toFinset.mp hi)
    have hm : ∀ b ∈ finitePackets bs, mass b.1 = ∑ i ∈ b.1, f i :=
      fun b hb => hmass b.1 (hlabels' b hb)
    have hm' : ∀ b ∈ finitePackets bs, mass' b.1 = ∑ i ∈ b.1, g i :=
      fun b hb => hmass' b.1 (hlabels' b hb)
    refine ⟨DataCertificate.mk (finitePackets bs) ?_ ⟨e,by omega⟩ hlabels' ?_ ?_ ?_⟩
    · simpa [finitePackets,List.map_map,Function.comp_def] using hnegative
    · exact Quot.sound ((finite_packets_perm bs hndall).trans
        ((List.Perm.of_eq hword).trans hperm))
    · apply (finiteChecks_equiv mass f C 0 (finitePackets bs) hm).mpr
      exact (finite_packet_checks f C 0 bs hndall).mpr holdchecks
    · apply (finiteEarChecks_equiv mass' g D E 0 k e hear (finitePackets bs) hm').mpr
      exact (finite_ear_checks g D 0 k e bs hndall).mpr hnewchecks
  · rintro ⟨cert⟩
    let bs := orderedPackets (DataCertificate.packets cert)
    have hperm : (blocksWord bs).Perm (List.range k) := Multiset.coe_eq_coe.mp (DataCertificate.partition cert)
    have hbslen : bs.length = 4 := by
      have hh := (DataCertificate.negativeOrder cert).length_eq
      simpa [bs,orderedPackets,hnglen] using hh
    have hpold : ∀ b ∈ bs, ∀ i ∈ b.1, 0 ≤ f i := by
      intro b hb i hi
      obtain ⟨b',hb',rfl⟩ := List.mem_map.mp hb
      have hp := (DataCertificate.positiveLabels cert) b' hb' i (Finset.mem_toList.mp hi)
      have hs := hsign i hp.1
      rw [if_neg hp.2] at hs
      exact hs.1.le
    have hpnew : ∀ b ∈ bs, ∀ i ∈ b.1, 0 ≤ g i := by
      intro b hb i hi
      obtain ⟨b',hb',rfl⟩ := List.mem_map.mp hb
      have hp := (DataCertificate.positiveLabels cert) b' hb' i (Finset.mem_toList.mp hi)
      have hs := hsign i hp.1
      rw [if_neg hp.2] at hs
      exact hs.2.le
    have hnegs : (bs.map Prod.snd).Perm ng := by
      simpa [bs,orderedPackets,List.map_map,Function.comp_def] using (DataCertificate.negativeOrder cert)
    have hnegative (v : ℕ) (hv : v ∈ bs.map Prod.snd) : f v ≤ 0 ∧ g v ≤ 0 := by
      have hn := hnegs.mem_iff.mp hv
      have hs := hsign v (hngrange v hn)
      rw [if_pos hn] at hs
      exact ⟨hs.1.le,hs.2.le⟩
    have hnegf : ∀ b ∈ bs, f b.2 ≤ 0 :=
      fun b hb => (hnegative b.2 (List.mem_map.mpr ⟨b,hb,rfl⟩)).1
    have hmarkedpos := withEar_positive g k (DataCertificate.earSlot cert).val bs
      (by rw [hear]; exact hE.le) hpnew
    have hmarkedneg : ∀ b ∈ withEar k (DataCertificate.earSlot cert).val bs, g b.2 ≤ 0 := by
      intro b hb
      apply (hnegative b.2 _).2
      rw [← withEar_negatives k (DataCertificate.earSlot cert).val bs]
      exact List.mem_map.mpr ⟨b,hb,rfl⟩
    have hm : ∀ b ∈ (DataCertificate.packets cert), mass b.1 = ∑ i ∈ b.1, f i :=
      fun b hb => hmass b.1 ((DataCertificate.positiveLabels cert) b hb)
    have hm' : ∀ b ∈ (DataCertificate.packets cert), mass' b.1 = ∑ i ∈ b.1, g i :=
      fun b hb => hmass' b.1 ((DataCertificate.positiveLabels cert) b hb)
    have hold := (strip_iff_packetChecks f C 0 bs ⟨by omega,hC⟩ hpold hnegf).mpr
      ((finiteChecks_equiv mass f C 0 (DataCertificate.packets cert) hm).mp (DataCertificate.oldEndpoints cert))
    have hnew := (strip_iff_packetChecks g D 0 (withEar k (DataCertificate.earSlot cert).val bs) ⟨by omega,hD⟩
      hmarkedpos hmarkedneg).mpr
      ((finiteEarChecks_equiv mass' g D E 0 k (DataCertificate.earSlot cert).val hear (DataCertificate.packets cert) hm').mp (DataCertificate.newEndpoints cert))
    obtain ⟨pre,post,hword,hmarked⟩ := withEar_split k (DataCertificate.earSlot cert).val bs (by omega)
    have hcut : pre.length ≤ k := by
      have hh := hperm.length_eq
      rw [hword] at hh
      simp only [List.length_append,List.length_range] at hh
      omega
    refine ⟨blocksWord bs,hperm,hold,pre.length,hcut,?_⟩
    rw [hword]
    simpa [insertAt,hmarked] using hnew

end D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
