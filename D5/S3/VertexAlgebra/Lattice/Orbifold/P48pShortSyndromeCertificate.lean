/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48pShortSyndromeCertificate
   generality: I
   mirror-B: none(waiver:no-B-plane-mirror-for-source-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/VertexAlgebra/Lattice/Orbifold/P48pShortSyndrome.p48p_short_syndrome_injective; instance=D5/S3/VertexAlgebra/Lattice/Orbifold/P48pShortSyndromeCertificate.all_bucket_nodup
   digest: The radix checker certifies distinct packed keys in all 27 P48p buckets. -/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.FinCases
import OmegaBuild.Commands

compile_only_with_mathlib

/-!
# Arithmetic certificate for P48p short syndromes

The packed column data produce a list of full nineteen-trit keys for each
of the 27 low-trit residues. Each list has pairwise distinct keys.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48pShortSyndromeCertificate

/-- Read base-eight lanes, reduce each modulo three, and pack the resulting trits. -/
def transcode : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, wide => wide % 8 % 3 + 3 * transcode n (wide / 8)

/- Each coordinate contributes two carry-free columns, for coefficients 1
   and 2. The table stores only these 96 numbers. -/
def columnData : Array (ℕ × ℕ) := #[
  (22588916653883393, 38316880750444546), (598213785027136, 351999417910400),
  (137711648768, 68855824384), (36310271995707392, 18577348462968832),
  (568447528865858, 290820859371649), (18018933994946560, 36037661831462912),
  (290417098626176, 567433899287104), (22597798763467336, 38321425060275344),
  (2252349603119104, 4504699155808256), (78517411904, 157034811520),
  (562960707616768, 281493263876096), (5094133465089, 9981655515138),
  (2537810309947528, 5075414410334288), (642734373274640, 322296510185992),
  (41131641357280320, 20618610326147712), (2326575194603649, 4547597272940610),
  (598145065550465, 351861978956866), (36030035060065416, 18015019165811280),
  (18577898220814336, 36311371511496704), (70919842168832, 36286165417984),
  (4535489658880, 8864814596096), (18613772086149248, 36381260595068992),
  (18023194892502082, 36033195235639937), (361268091327048, 603788920562832),
  (5066635513693258, 2533420836061841), (22588437750095872, 38315919721631744),
  (22527430052843592, 38286240704962704), (74835546120705, 44117925630978),
  (40602784885645824, 20301392644150272), (36063981391052800, 18084767253659648),
  (571764300652544, 285883760939008), (4539883511088130, 2322718313677313),
  (4543182081630720, 2330964671861760), (2533291975017545, 5066558173151890),
  (619584684032, 1239119036416), (36311457410842698, 18578044249702545),
  (79251978059776, 39730880184320), (35186788008520, 70369952138384),
  (633938515591185, 317898581344266), (2814758375923856, 4785091821703240),
  (36099165767598080, 18049582884192256), (36283884240896, 70918500253696),
  (22518075748516872, 38280751602991632), (36069000211366474, 18094801673061521),
  (551097991168, 1101793329152), (70387018760784, 35195145159816),
  (43990128792066, 74786118050817), (36029965384287234, 18015085972685313)
]

/- The partitioned generator tests the low three trits at each leaf.  A
   retained key still stores the full nineteen-trit transcode. -/
def sparseKeysBucket (bucket : Fin 27) (finish : ℕ → ℕ) :
    List (ℕ × ℕ) → ℕ → ℕ → List ℕ
  | [], _, acc =>
      if transcode 3 acc = bucket.val then [finish acc] else []
  | _ :: _, 0, acc =>
      if transcode 3 acc = bucket.val then [finish acc] else []
  | ab :: rest, budget + 1, acc =>
      sparseKeysBucket bucket finish rest budget (acc + ab.1) ++
      sparseKeysBucket bucket finish rest budget (acc + ab.2) ++
      sparseKeysBucket bucket finish rest (budget + 1) acc

def bucketKeys (bucket : Fin 27) : List ℕ :=
  sparseKeysBucket bucket (transcode 19)
    ((List.finRange 48).map fun i => columnData.getD i.val (0, 0)) 3 0

/- Refine the finite order by descending bits of the exact keys, testing each
   bucket for a singleton or an empty list. Each level takes a linear pass. -/
private def radixDistinct : ℕ → List ℕ → Bool
  | _, [] => true
  | _, [_] => true
  | 0, _ :: _ :: _ => false
  | bit + 1, x :: y :: rest =>
      let halves := (x :: y :: rest).partition (fun k => k.testBit bit)
      radixDistinct bit halves.1 && radixDistinct bit halves.2

private theorem nodup_of_partition (p : ℕ → Bool) (ks : List ℕ)
    (ht : (ks.partition p).1.Nodup) (hf : (ks.partition p).2.Nodup) : ks.Nodup := by
  rw [List.partition_eq_filter_filter] at ht hf
  change (ks.filter p).Pairwise (· ≠ ·) at ht
  change (ks.filter (not ∘ p)).Pairwise (· ≠ ·) at hf
  have ht' := List.pairwise_filter.mp ht
  have hf' := List.pairwise_filter.mp hf
  apply (ht'.and hf').imp
  rintro a b ⟨h₁, h₂⟩ rfl
  cases hp : p a with
  | false => exact h₂ (by simp [hp]) (by simp [hp]) rfl
  | true => exact h₁ (by simp [hp]) (by simp [hp]) rfl

private theorem radixDistinct_sound (bits : ℕ) (ks : List ℕ)
    (h : radixDistinct bits ks = true) : ks.Nodup := by
  induction bits generalizing ks with
  | zero =>
    rcases ks with _ | ⟨x, _ | ⟨y, rest⟩⟩
    · simp
    · simp
    · simp [radixDistinct] at h
  | succ bit ih =>
    rcases ks with _ | ⟨x, _ | ⟨y, rest⟩⟩
    · simp
    · simp
    · simp only [radixDistinct, Bool.and_eq_true] at h
      exact nodup_of_partition _ _ (ih _ h.1) (ih _ h.2)

/- The 27 checks are independent kernel decisions. Their source list has
   142,977 exact keys, and the largest bucket has 11,901 retained keys. -/
set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_0 : (bucketKeys 0).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_1 : (bucketKeys 1).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_2 : (bucketKeys 2).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_3 : (bucketKeys 3).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_4 : (bucketKeys 4).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_5 : (bucketKeys 5).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_6 : (bucketKeys 6).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_7 : (bucketKeys 7).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_8 : (bucketKeys 8).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_9 : (bucketKeys 9).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_10 : (bucketKeys 10).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_11 : (bucketKeys 11).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_12 : (bucketKeys 12).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_13 : (bucketKeys 13).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_14 : (bucketKeys 14).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_15 : (bucketKeys 15).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_16 : (bucketKeys 16).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_17 : (bucketKeys 17).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_18 : (bucketKeys 18).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_19 : (bucketKeys 19).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_20 : (bucketKeys 20).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_21 : (bucketKeys 21).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_22 : (bucketKeys 22).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_23 : (bucketKeys 23).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_24 : (bucketKeys 24).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_25 : (bucketKeys 25).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
private theorem bucket_nodup_26 : (bucketKeys 26).Nodup := by
  apply radixDistinct_sound 31
  decide +kernel

theorem all_bucket_nodup (bucket : Fin 27) :
    (bucketKeys bucket).Nodup := by
  fin_cases bucket
  · exact bucket_nodup_0
  · exact bucket_nodup_1
  · exact bucket_nodup_2
  · exact bucket_nodup_3
  · exact bucket_nodup_4
  · exact bucket_nodup_5
  · exact bucket_nodup_6
  · exact bucket_nodup_7
  · exact bucket_nodup_8
  · exact bucket_nodup_9
  · exact bucket_nodup_10
  · exact bucket_nodup_11
  · exact bucket_nodup_12
  · exact bucket_nodup_13
  · exact bucket_nodup_14
  · exact bucket_nodup_15
  · exact bucket_nodup_16
  · exact bucket_nodup_17
  · exact bucket_nodup_18
  · exact bucket_nodup_19
  · exact bucket_nodup_20
  · exact bucket_nodup_21
  · exact bucket_nodup_22
  · exact bucket_nodup_23
  · exact bucket_nodup_24
  · exact bucket_nodup_25
  · exact bucket_nodup_26

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48pShortSyndromeCertificate
