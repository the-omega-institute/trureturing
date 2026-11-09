/- GID: D5/S3/Combinatorics/Games/CrimFourPartClassification
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Games/CrimFourPartClassification
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Classifies all losing four-part CRIM positions without a bound on the parts. -/

/-
admission_basis: open-problem-resolution (#23809; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25535
Direct frozen dependencies: the declaration identities below are from the baseline Lean report.
Baseline: 124988ed10cb12637ab3b0610dd6ed04202aff31. Publicized identities are the original private declarations.
The owner prefix for each dependency GID is D5/S0/Certificates/Games/CrimGrundyRefutation.
Position: sha256:7fad6c645bb27adb6b1ae338d518a43cf73268c3c78a44a55b9f55564efd032c
conjugate: sha256:eb78ae547b75f4106a17279e9a30ecafcb76ab8feb8fd217a0d8e865fe78d781
grundy: sha256:6f49a3cea2bf0bb7e16d4457d67241dc84498255f3f2c11f6e0bd76e28a4798f
grundy_eq: sha256:a74c779d3dfe83c3aa21351f29f835c5c7fd54c58c2b571626d30d814a1749c3
height: sha256:e826e8a413916f2ff75dad8c80a0a9378a691a0bed1d469df4086f83b692d007
mex: sha256:0738bcb6bb6cf5e757f0f1af9901368f863881b2fcbf2dce0386cf7450eb031d
mex_spec: sha256:dad28424985fb7ac4bdbd2bce2995c3a0490e168af57bfc8286a5352b0dce7a7
move_decreases: sha256:6f94fe468a235d149f233be83c96b2aac34fa640fb0fe1875d14b67f12121bc5
moves: sha256:384246dce8fb66a2497a03b15606796cbcad7c6f60ec078a16745f17d5422df0
rowMoves: sha256:b081efa3a150cdd0d0406380c6dfdae2256457cf0ba14c3bb5e89813b86d298b
sum_nonzero: sha256:eaf560818e47a07161b6bb518bec6b2427fb516dda45c945c136cbb827719013
The four-clause claim retains #23809 exactly and uses the original CRIM evaluator.
Each dependency list below expands same-module helpers and refers to these declaration identities.
Proof shapes are semantic classifications; no escape witness is asserted for this admission basis.
claim: proof_shape: not-applicable (definition); escape_witness: none;
  Direct frozen dependencies: grundy; consumers: result.
nz: proof_shape: not-applicable (definition); escape_witness: none;
  Direct frozen dependencies: Position; consumers: p4, height_nz, filtered_range_stable, conjugate_bounded, conjugate_nz, conjugate_p4, conjugate_blocks, rowMoves_nz, mem_rowMoves_p4.
p4: proof_shape: not-applicable (definition); escape_witness: none;
  Direct frozen dependencies: Position; consumers: conjugate_p4, conjugate_blocks, mem_rowMoves_p4, conjugate_rawBlocks, column_moves_p4, moves_p4, classification, result.
rawBlocks: proof_shape: not-applicable (definition); escape_witness: none;
  Direct frozen dependencies: Position; consumers: conjugate_p4, conjugate_blocks, conjugate_rawBlocks, mem_rowMoves_rawBlocks, column_moves_p4.
height_nil: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: height; consumers: height_append, height_replicate, conjugate_p4.
height_cons: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: Position, height; consumers: height_append, height_replicate, height_nz, height_zero_of_bound, conjugate_p4.
rowMoves_cons: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: Position, rowMoves; consumers: rowMoves_append, rowMoves_replicate, rowMoves_nz, mem_rowMoves_p4.
height_append: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: Position, height; consumers: conjugate_blocks.
height_replicate: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: Position, height; consumers: conjugate_blocks.
height_nz: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: Position, height; consumers: conjugate_nz.
height_zero_of_bound: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: Position, height; consumers: filtered_range_stable.
filtered_range_stable: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: Position, height; consumers: conjugate_bounded.
conjugate_bounded: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: Position, conjugate, height; consumers: conjugate_p4, conjugate_blocks.
conjugate_nz: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: Position, conjugate, height, sum_nonzero; consumers: conjugate_p4.
map_range_interval: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: conjugate_p4.
conjugate_p4: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: Position, conjugate, height, sum_nonzero; consumers: column_moves_p4.
conjugate_blocks: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: Position, conjugate, height; consumers: conjugate_rawBlocks.
rowMoves_append: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: Position, rowMoves; consumers: mem_rowMoves_rawBlocks.
rowMoves_replicate: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: Position, rowMoves; consumers: mem_rowMoves_rawBlocks.
rowMoves_nz: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: Position, rowMoves; consumers: mem_rowMoves_p4.
mem_rowMoves_p4: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: Position, rowMoves; consumers: moves_p4.
conjugate_rawBlocks: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: Position, conjugate, height; consumers: column_moves_p4.
mem_rowMoves_rawBlocks: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: Position, rowMoves; consumers: column_moves_p4.
four: proof_shape: not-applicable (definition); escape_witness: none;
  Direct frozen dependencies: none; consumers: P, no_P_follower, non_P_has_follower, result.
P: proof_shape: not-applicable (definition); escape_witness: none;
  Direct frozen dependencies: none; consumers: no_P_follower, non_P_has_follower, classification, result.
Next: proof_shape: not-applicable (definition); escape_witness: none;
  Direct frozen dependencies: none; consumers: next_order, no_P_follower, non_P_has_follower, moves_p4, classification.
next_order: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: classification.
no_P_follower: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: classification.
non_P_has_follower: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: none; consumers: classification.
column_moves_p4: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: Position, conjugate, height, rowMoves, sum_nonzero; consumers: moves_p4.
moves_p4: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: Position, conjugate, height, moves, rowMoves, sum_nonzero; consumers: classification.
classification: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: Position, conjugate, grundy, grundy_eq, height, mex, mex_spec, move_decreases, moves, rowMoves, sum_nonzero; consumers: result.
result: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: Position, conjugate, grundy, grundy_eq, height, mex, mex_spec, move_decreases, moves, rowMoves, sum_nonzero; consumers: terminal settlement.
-/

import D5.S0.Certificates.Games.CrimGrundyRefutation


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Games.CrimFourPartClassification

open D5.S0.Certificates.Games.CrimGrundyRefutation

/-!
Binding conventions for Bašić–Gottlieb–Krnc, arXiv:2606.16828v1,
Section 5, Question 1. The imported owner supplies Position, rowMoves,
height, conjugate, moves, mex, and grundy without redefining them.
On the positive nonincreasing lists quantified below they are exactly
the source's partitions, row deletions, and conjugate-row-conjugate
column deletions. Normal-play losing means grundy equals zero.
Question 1 asks for a classification; claim states the proposed complete
answer on its full domain, with no upper bound on any part.
-/

def claim : Prop :=
  ∀ a b c d : ℕ, 1 ≤ d → d ≤ c → c ≤ b → b ≤ a →
    (grundy [a, b, c, d] = 0 ↔
      a % 2 = 0 ∧
        ((2 ≤ d ∧ ¬ (b % 2 = 1 ∧ c % 2 = 1)) ∨
         (d = 1 ∧ c = 1 ∧ (b % 2 = 0 ∨ b = 1)) ∨
         (d = 1 ∧ 2 ≤ c ∧ b % 2 = 1) ∨
         (d = 1 ∧ c = 2 ∧ (3 ≤ b ∨ a = 2))))

end D5.S3.Combinatorics.Games.CrimFourPartClassification


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.Games.CrimFourPartClassification
open D5.S0.Certificates.Games.CrimGrundyRefutation

private abbrev nz (p : Position) : Position := p.filter (· != 0)
private def p4 (a b c d : ℕ) : Position := nz [a,b,c,d]
private def rawBlocks (n4 n3 n2 n1 : ℕ) : Position :=
  List.replicate n4 4 ++ List.replicate n3 3 ++
  List.replicate n2 2 ++ List.replicate n1 1

@[simp] private theorem height_nil (j : ℕ) : height [] j = 0 := by
  exact Nat.eq_zero_of_add_eq_zero_left rfl
@[simp] private theorem height_cons (n : ℕ) (p : Position) (j : ℕ) :
    height (n::p) j = (if j<n then 1 else 0) + height p j := by
  exact Eq.symm (Nat.add_zero ((if j < n then 1 else 0).add (height p j)))
@[simp] private theorem rowMoves_cons (n : ℕ) (p : Position) :
    rowMoves (n::p) = (if n=0 then [] else [p]) ++ (rowMoves p).map (n::·) := by
  exact List.toList_toArray

private theorem height_append (p q : Position) (j : ℕ) :
    height (p ++ q) j = height p j + height q j := by
  induction p with
  | nil => simp only [height_nil, List.nil_append, Nat.zero_add]
  | cons n p ih => simp only [List.cons_append, height_cons, ih]; omega

private theorem height_replicate (n k j : ℕ) :
    height (List.replicate n k) j = if j < k then n else 0 := by
  induction n with
  | zero => simp [height_nil]
  | succ n ih =>
    simp only [List.replicate_succ, height_cons, ih]
    split_ifs <;> omega

private theorem height_nz (p : Position) (j : ℕ) : height (nz p) j = height p j := by
  induction p with
  | nil => rfl
  | cons n p ih =>
    by_cases hn : n = 0
    · subst n; simpa [nz] using ih
    · simpa [nz, hn] using ih

private theorem height_zero_of_bound (p : Position) (w j : ℕ)
    (hw : ∀ n ∈ p, n ≤ w) (hj : w ≤ j) : height p j = 0 := by
  induction p with
  | nil => rfl
  | cons n p ih =>
    have hn := hw n (by simp)
    have hi := ih (fun x hx => hw x (by simp [hx]))
    simp [height_cons, show ¬j < n by omega, hi]

private theorem filtered_range_stable (p : Position) (w k : ℕ)
    (hw : ∀ n ∈ p, n ≤ w) :
    nz ((List.range (w+k)).map (height p)) = nz ((List.range w).map (height p)) := by
  rw [List.range_add, List.map_append]
  simp only [nz, List.filter_append]
  have hz : (((List.range k).map (w + ·)).map (height p)).filter (· != 0) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    simp [height_zero_of_bound p w (w+i) hw (by omega)]
  rw [hz, List.append_nil]

private theorem conjugate_bounded (p : Position) (w : ℕ)
    (hw : ∀ n ∈ p, n ≤ w) :
    conjugate p = nz ((List.range w).map (height p)) := by
  unfold conjugate
  by_cases hs : w ≤ p.sum
  · have he : p.sum = w + (p.sum-w) := by exact Eq.symm (Nat.add_sub_of_le hs)
    rw [he]
    exact filtered_range_stable p w (p.sum-w) hw
  · have hb : ∀ n ∈ p, n ≤ p.sum :=
      fun n hn => List.single_le_sum (fun x _ => Nat.zero_le x) n hn
    have he : w = p.sum + (w-p.sum) := by omega
    rw [he]
    exact (filtered_range_stable p p.sum (w-p.sum) hb).symm

private theorem conjugate_nz (p : Position) : conjugate (nz p) = conjugate p := by
  unfold conjugate
  rw [sum_nonzero]
  rw [show height (nz p) = height p from funext (height_nz p)]

private theorem map_range_interval (f : ℕ → ℕ) (start count value : ℕ)
    (hf : ∀ j, start ≤ j → j < start+count → f j = value) :
    ((List.range count).map (start + ·)).map f = List.replicate count value := by
  rw [List.map_map, Function.comp_def]
  have h : ∀ i ∈ List.range count, f (start+i) = value := by
    intro i hi
    exact hf (start+i) (by omega) (by simp only [List.mem_range] at hi; omega)
  simpa only [List.length_range, Function.comp_apply] using List.map_eq_replicate_iff.mpr h

private theorem conjugate_p4 (a b c d : ℕ) (hba : b ≤ a) (hcb : c ≤ b) (hdc : d ≤ c) :
    conjugate (p4 a b c d) = rawBlocks d (c-d) (b-c) (a-b) := by
  have hb : ∀ n ∈ [a,b,c,d], n ≤ a := by intro n hn; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn; omega
  have hr : List.range a =
      ((List.range d ++ (List.range (c-d)).map (d+·)) ++
      (List.range (b-c)).map (c+·)) ++ (List.range (a-b)).map (b+·) := by
    calc
      List.range a = List.range b ++ (List.range (a-b)).map (b+·) := by
        rw [←List.range_add]; congr 1; omega
      _ = (List.range c ++ (List.range (b-c)).map (c+·)) ++
          (List.range (a-b)).map (b+·) := by
        congr 1
        rw [←List.range_add]; congr 1; omega
      _ = _ := by
        congr 2
        rw [←List.range_add]; congr 1; omega
  have e4 : (List.range d).map (height [a,b,c,d]) = List.replicate d 4 := by
    simpa using map_range_interval (height [a,b,c,d]) 0 d 4 (by
      intro j hj hu
      simp only [height_cons,height_nil]
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)])
  have e3 := map_range_interval (height [a,b,c,d]) d (c-d) 3 (by
    intro j hj hu
    simp only [height_cons,height_nil]
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)])
  have e2 := map_range_interval (height [a,b,c,d]) c (b-c) 2 (by
    intro j hj hu
    simp only [height_cons,height_nil]
    rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega)])
  have e1 := map_range_interval (height [a,b,c,d]) b (a-b) 1 (by
    intro j hj hu
    simp only [height_cons,height_nil]
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)])
  rw [p4, conjugate_nz, conjugate_bounded _ a hb, hr]
  simp only [List.map_append]
  rw [e4,e3,e2,e1]
  simp [nz, rawBlocks, List.append_assoc]

private theorem conjugate_blocks (a b c d : ℕ) (hba : b ≤ a) (hcb : c ≤ b) (hdc : d ≤ c) :
    conjugate (rawBlocks d (c-d) (b-c) (a-b)) = p4 a b c d := by
  have hb : ∀ n ∈ rawBlocks d (c-d) (b-c) (a-b), n ≤ 4 := by
    intro n hn
    simp only [rawBlocks, List.mem_append, List.mem_replicate] at hn
    omega
  rw [conjugate_bounded _ 4 hb]
  have h0 : height (rawBlocks d (c-d) (b-c) (a-b)) 0 = a := by
    simp [rawBlocks,height_append,height_replicate]; omega
  have h1 : height (rawBlocks d (c-d) (b-c) (a-b)) 1 = b := by
    simp [rawBlocks,height_append,height_replicate]; omega
  have h2 : height (rawBlocks d (c-d) (b-c) (a-b)) 2 = c := by
    simp [rawBlocks,height_append,height_replicate]; omega
  have h3 : height (rawBlocks d (c-d) (b-c) (a-b)) 3 = d := by
    simp [rawBlocks,height_append,height_replicate]
  change nz ([height (rawBlocks d (c-d) (b-c) (a-b)) 0,height (rawBlocks d (c-d) (b-c) (a-b)) 1,
    height (rawBlocks d (c-d) (b-c) (a-b)) 2,height (rawBlocks d (c-d) (b-c) (a-b)) 3]) = p4 a b c d
  rw [h0,h1,h2,h3]
  rfl

private theorem rowMoves_append (p q : Position) :
    rowMoves (p++q) = ((rowMoves p).map (·++q)) ++ ((rowMoves q).map (p++·)) := by
  induction p with
  | nil => simp [(show rowMoves [] = [] from rfl)]
  | cons n p ih =>
    by_cases hn : n = 0 <;>
      simp [rowMoves_cons, hn, ih, List.map_append, List.map_map,
        List.cons_append, Function.comp_def]

private theorem rowMoves_replicate (n k : ℕ) (hk : k ≠ 0) :
    rowMoves (List.replicate n k) = List.replicate n (List.replicate (n-1) k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, rowMoves_cons, if_neg hk, ih]
    cases n <;> simp [List.replicate_succ, List.map_replicate]

private theorem rowMoves_nz (p : Position) :
    rowMoves (nz p) = (rowMoves p).map nz := by
  induction p with
  | nil => rfl
  | cons n p ih =>
    by_cases hn : n = 0 <;>
      simp [nz, hn, rowMoves_cons,ih, List.map_map, Function.comp_def] at *

private theorem mem_rowMoves_p4 (a b c d : ℕ) (q : Position) :
    q ∈ rowMoves (p4 a b c d) ↔
    (0<a ∧ q=p4 b c d 0) ∨ (0<b ∧ q=p4 a c d 0) ∨
    (0<c ∧ q=p4 a b d 0) ∨ (0<d ∧ q=p4 a b c 0) := by
  rw [p4, rowMoves_nz]
  simp only [rowMoves_cons, (show rowMoves [] = [] from rfl), List.map_append, List.map_map, List.map_nil,
    List.mem_append, List.mem_map]
  by_cases ha : a=0 <;> by_cases hb : b=0 <;>
    by_cases hc : c=0 <;> by_cases hd : d=0 <;>
    simp [ha,hb,hc,hd,p4,nz, Nat.pos_iff_ne_zero] <;> aesop


private theorem conjugate_rawBlocks (n4 n3 n2 n1 : ℕ) :
    conjugate (rawBlocks n4 n3 n2 n1) =
      p4 (n4+n3+n2+n1) (n4+n3+n2) (n4+n3) n4 := by
  have hb : rawBlocks n4 n3 n2 n1 =
      rawBlocks n4 ((n4+n3)-n4) ((n4+n3+n2)-(n4+n3)) ((n4+n3+n2+n1)-(n4+n3+n2)) := by
    simp [rawBlocks]
  rw [hb, conjugate_blocks] <;> omega

private theorem mem_rowMoves_rawBlocks (n4 n3 n2 n1 : ℕ) (q : Position) :
    q ∈ rowMoves (rawBlocks n4 n3 n2 n1) ↔
      (0<n4 ∧ q=rawBlocks (n4-1) n3 n2 n1) ∨
      (0<n3 ∧ q=rawBlocks n4 (n3-1) n2 n1) ∨
      (0<n2 ∧ q=rawBlocks n4 n3 (n2-1) n1) ∨
      (0<n1 ∧ q=rawBlocks n4 n3 n2 (n1-1)) := by
  simp [rawBlocks,rowMoves_append,rowMoves_replicate, List.map_append,
    List.append_assoc,Nat.pos_iff_ne_zero, eq_comm]

end D5.S3.Combinatorics.Games.CrimFourPartClassification

namespace D5.S3.Combinatorics.Games.CrimFourPartClassification

private def four (a b c d : ℕ) : Prop :=
  a % 2 = 0 ∧
    ((2 ≤ d ∧ ¬ (b % 2 = 1 ∧ c % 2 = 1)) ∨
     (d = 1 ∧ c = 1 ∧ (b % 2 = 0 ∨ b = 1)) ∨
     (d = 1 ∧ 2 ≤ c ∧ b % 2 = 1) ∨
     (d = 1 ∧ c = 2 ∧ (3 ≤ b ∨ a = 2)))

private def P (a b c d : ℕ) : Prop :=
  (a = 0) ∨
  (0 < b ∧ c = 0 ∧ a % 2 = 0) ∨
  (0 < c ∧ d = 0 ∧ 1 < a ∧ a % 2 = 1 ∧ b % 2 = 1 ∧ (1 < c ∨ b = 1)) ∨
  (0 < d ∧ four a b c d)

private def Next (a b c d e f g h : ℕ) : Prop :=
  (0<a ∧ (e,f,g,h)=(b,c,d,0)) ∨
  (0<b ∧ (e,f,g,h)=(a,c,d,0)) ∨
  (0<c ∧ (e,f,g,h)=(a,b,d,0)) ∨
  (0<d ∧ (e,f,g,h)=(a,b,c,0)) ∨
  (b<a ∧ (e,f,g,h)=(a-1,b,c,d)) ∨
  (c<b ∧ (e,f,g,h)=(a-1,b-1,c,d)) ∨
  (d<c ∧ (e,f,g,h)=(a-1,b-1,c-1,d)) ∨
  (0<d ∧ (e,f,g,h)=(a-1,b-1,c-1,d-1))

private theorem next_order (a b c d e f g h : ℕ)
    (hba : b≤a) (hcb : c≤b) (hdc : d≤c)
    (hn : Next a b c d e f g h) : f≤e ∧ g≤f ∧ h≤g := by
  simp only [Next, Prod.mk.injEq] at hn
  omega

private theorem no_P_follower (a b c d e f g h : ℕ)
    (hba : b≤a) (hcb : c≤b) (hdc : d≤c)
    (hp : P a b c d) (hn : Next a b c d e f g h) : ¬ P e f g h := by
  simp only [Next, Prod.mk.injEq] at hn
  rcases hn with hn|hn|hn|hn|hn|hn|hn|hn
  all_goals
    obtain ⟨hg, he, hf, hgg, hh⟩ := hn
    subst e; subst f; subst g; subst h
    simp only [P, four] at *
    omega

private theorem non_P_has_follower (a b c d : ℕ)
    (hba : b≤a) (hcb : c≤b) (hdc : d≤c) (hp : ¬ P a b c d) :
    ∃ e f g h : ℕ, Next a b c d e f g h ∧ P e f g h := by
  unfold Next
  by_cases hd : d=0
  · by_cases hc : c=0
    · by_cases hb : b=0
      · refine ⟨0,0,0,0,?_,?_⟩
        · apply Or.inl; simp only [Prod.mk.injEq]; simp only [P,four] at hp; simp_all [] <;> omega
        · simp [P]
      · by_cases ha : a%2=0
        · exact False.elim (hp (Or.inr (Or.inl ⟨by simp_all [P,four] <;> omega,hc,ha⟩)))
        · by_cases haa : a=1
          · refine ⟨0,0,0,0,?_,by simp [P]⟩
            apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
            simp only [Prod.mk.injEq]; simp_all [P,four] <;> omega
          · by_cases hab : b<a
            · refine ⟨a-1,b,0,0,?_,?_⟩
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hab,by simp [hc,hd]⟩))))
              · simp only [P,four]; simp_all [P,four] <;> omega
            · refine ⟨a-1,b-1,0,0,?_,?_⟩
              · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
                simp only [Prod.mk.injEq]; simp_all [P,four] <;> omega
              · simp only [P,four]; simp_all [P,four] <;> omega
    · by_cases ha : a%2=0
      · refine ⟨a,c,0,0,?_,?_⟩
        · exact Or.inr (Or.inl ⟨by simp_all [P,four] <;> omega,by simp [hd]⟩)
        · simp only [P,four]; simp_all [P,four] <;> omega
      · by_cases hb : b%2=0
        · refine ⟨b,c,0,0,?_,?_⟩
          · exact Or.inl ⟨by simp_all [P,four] <;> omega,by simp [hd]⟩
          · simp only [P,four]; simp_all [P,four] <;> omega
        · by_cases haa : a=1
          · refine ⟨0,0,0,0,?_,by simp [P]⟩
            apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
            simp only [Prod.mk.injEq]; simp_all [P,four] <;> omega
          · have hc1 : c=1 := by
              by_contra hcc
              apply hp
              exact Or.inr (Or.inr (Or.inl ⟨by omega,hd,by omega,by omega,by omega,
                Or.inl (by omega)⟩))
            have hb2 : 1<b := by
              by_contra hbb
              apply hp
              exact Or.inr (Or.inr (Or.inl ⟨by omega,hd,by omega,by omega,by omega,
                Or.inr (by omega)⟩))
            refine ⟨a-1,b-1,0,0,?_,?_⟩
            · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
              exact ⟨by omega,by simp [hc1,hd]⟩
            · exact Or.inr (Or.inl ⟨by omega,rfl,by omega⟩)

  · by_cases ha : a%2=0
    · by_cases hdd : 1<d
      · refine ⟨b,c,d,0,Or.inl ⟨by simp_all [P,four] <;> omega,rfl⟩,?_⟩
        simp only [P,four] at *; simp_all [] <;> omega
      · by_cases hc : c=1
        · refine ⟨b,1,1,0,?_,?_⟩
          · apply Or.inl; simp only [Prod.mk.injEq]; simp_all [P,four] <;> omega
          · simp only [P,four] at *; simp_all [] <;> omega
        · refine ⟨a-1,b-1,c-1,0,?_,?_⟩
          · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
            simp only [Prod.mk.injEq]; simp_all [P,four] <;> omega
          · simp only [P,four] at *; simp_all [] <;> omega
    · by_cases haa : a=1
      · refine ⟨0,0,0,0,?_,by simp [P]⟩
        apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
        simp only [Prod.mk.injEq]; simp_all [P,four] <;> omega
      · by_cases hc : c=1
        · by_cases hb : b=1
          · refine ⟨a-1,1,1,1,?_,?_⟩
            · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
              simp only [Prod.mk.injEq]; simp_all [P,four] <;> omega
            · simp only [P,four]; simp_all [P,four] <;> omega
          · refine ⟨a,1,1,0,?_,?_⟩
            · apply Or.inr ∘ Or.inl
              simp only [Prod.mk.injEq]; simp_all [P,four] <;> omega
            · simp only [P,four]; simp_all [P,four] <;> omega
        · by_cases hb : b%2=1
          · refine ⟨a,b,c,0,Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp_all [P,four] <;> omega,rfl⟩))),?_⟩
            simp only [P,four]; simp_all [P,four] <;> omega
          · by_cases hdd : 1<d
            · by_cases hcc : c%2=1
              · refine ⟨a,c,d,0,Or.inr (Or.inl ⟨by simp_all [P,four] <;> omega,rfl⟩),?_⟩
                simp only [P,four]; simp_all [P,four] <;> omega
              · refine ⟨a-1,b,c,d,?_,?_⟩
                · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
                  simp only []; simp_all [P,four] <;> omega
                · simp only [P,four]; simp_all [P,four] <;> omega
            · by_cases hcc : c%2=1
              · refine ⟨a-1,b-1,c,1,?_,?_⟩
                · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
                  simp only [Prod.mk.injEq]; simp_all [P,four] <;> omega
                · simp only [P,four]; simp_all [P,four] <;> omega
              · by_cases hccc : 4≤c
                · refine ⟨a-1,b-1,c-1,1,?_,?_⟩
                  · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
                    simp only [Prod.mk.injEq]; simp_all [P,four] <;> omega
                  · simp only [P,four]; simp_all [P,four] <;> omega
                · by_cases hbb : b=2
                  · refine ⟨a-1,1,1,1,?_,?_⟩
                    · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
                      simp only [Prod.mk.injEq]; simp_all [P,four] <;> omega
                    · simp only [P,four]; simp_all [P,four] <;> omega
                  · refine ⟨a-1,b,2,1,?_,?_⟩
                    · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
                      simp only [Prod.mk.injEq]; simp_all [P,four] <;> omega
                    · simp only [P,four]; simp_all [P,four] <;> omega
end D5.S3.Combinatorics.Games.CrimFourPartClassification

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Games.CrimFourPartClassification
open D5.S0.Certificates.Games.CrimGrundyRefutation

private theorem column_moves_p4 (a b c d : ℕ) (q : Position)
    (hba : b≤a) (hcb : c≤b) (hdc : d≤c) :
    q ∈ (rowMoves (conjugate (p4 a b c d))).map conjugate ↔
    (b<a ∧ q=p4 (a-1) b c d) ∨
    (c<b ∧ q=p4 (a-1) (b-1) c d) ∨
    (d<c ∧ q=p4 (a-1) (b-1) (c-1) d) ∨
    (0<d ∧ q=p4 (a-1) (b-1) (c-1) (d-1)) := by
  rw [conjugate_p4 a b c d hba hcb hdc]
  change q ∈ (rowMoves (rawBlocks d (c-d) (b-c) (a-b))).map conjugate ↔ _
  simp only [List.mem_map, mem_rowMoves_rawBlocks]
  constructor
  · rintro ⟨s,hs,rfl⟩
    rcases hs with ⟨hn,rfl⟩|⟨hn,rfl⟩|⟨hn,rfl⟩|⟨hn,rfl⟩
    · apply Or.inr ∘ Or.inr ∘ Or.inr
      refine ⟨hn,?_⟩
      rw [conjugate_rawBlocks]
      congr 1 <;> omega
    · apply Or.inr ∘ Or.inr ∘ Or.inl
      refine ⟨by omega,?_⟩
      rw [conjugate_rawBlocks]
      congr 1 <;> omega
    · apply Or.inr ∘ Or.inl
      refine ⟨by omega,?_⟩
      rw [conjugate_rawBlocks]
      congr 1 <;> omega
    · apply Or.inl
      refine ⟨by omega,?_⟩
      rw [conjugate_rawBlocks]
      congr 1 <;> omega
  · intro h
    rcases h with ⟨hn,rfl⟩|⟨hn,rfl⟩|⟨hn,rfl⟩|⟨hn,rfl⟩
    · refine ⟨rawBlocks d (c-d) (b-c) (a-b-1),?_,?_⟩
      · exact Or.inr (Or.inr (Or.inr ⟨by omega,rfl⟩))
      · rw [conjugate_rawBlocks]; congr 1 <;> omega
    · refine ⟨rawBlocks d (c-d) (b-c-1) (a-b),?_,?_⟩
      · exact Or.inr (Or.inr (Or.inl ⟨by omega,rfl⟩))
      · rw [conjugate_rawBlocks]; congr 1 <;> omega
    · refine ⟨rawBlocks d (c-d-1) (b-c) (a-b),?_,?_⟩
      · exact Or.inr (Or.inl ⟨by omega,rfl⟩)
      · rw [conjugate_rawBlocks]; congr 1 <;> omega
    · refine ⟨rawBlocks (d-1) (c-d) (b-c) (a-b),?_,?_⟩
      · exact Or.inl ⟨hn,rfl⟩
      · rw [conjugate_rawBlocks]; congr 1 <;> omega

private theorem moves_p4 (a b c d : ℕ) (q : Position)
    (hba : b≤a) (hcb : c≤b) (hdc : d≤c) :
    q ∈ moves (p4 a b c d) ↔
      ∃ e f g h : ℕ, Next a b c d e f g h ∧ q=p4 e f g h := by
  simp only [moves,List.mem_append,mem_rowMoves_p4,
    column_moves_p4 a b c d q hba hcb hdc]
  constructor
  · intro hm
    rcases hm with (h|h|h|h)|(h|h|h|h)
    · exact ⟨b,c,d,0,Or.inl ⟨h.1,rfl⟩,h.2⟩
    · exact ⟨a,c,d,0,Or.inr (Or.inl ⟨h.1,rfl⟩),h.2⟩
    · exact ⟨a,b,d,0,Or.inr (Or.inr (Or.inl ⟨h.1,rfl⟩)),h.2⟩
    · exact ⟨a,b,c,0,Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1,rfl⟩))),h.2⟩
    · exact ⟨a-1,b,c,d,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1,rfl⟩)))),h.2⟩
    · exact ⟨a-1,b-1,c,d,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1,rfl⟩))))),h.2⟩
    · exact ⟨a-1,b-1,c-1,d,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1,rfl⟩)))))),h.2⟩
    · exact ⟨a-1,b-1,c-1,d-1,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1,rfl⟩)))))),h.2⟩
  · rintro ⟨e,f,g,h,hn,rfl⟩
    simp only [Next,Prod.mk.injEq] at hn
    rcases hn with hn|hn|hn|hn|hn|hn|hn|hn
    all_goals
      obtain ⟨hx,he,hf,hg,hh⟩ := hn
      subst e; subst f; subst g; subst h
      first
      | exact Or.inl (Or.inl ⟨hx,rfl⟩)
      | exact Or.inl (Or.inr (Or.inl ⟨hx,rfl⟩))
      | exact Or.inl (Or.inr (Or.inr (Or.inl ⟨hx,rfl⟩)))
      | exact Or.inl (Or.inr (Or.inr (Or.inr ⟨hx,rfl⟩)))
      | exact Or.inr (Or.inl ⟨hx,rfl⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨hx,rfl⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hx,rfl⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hx,rfl⟩)))
end D5.S3.Combinatorics.Games.CrimFourPartClassification

namespace D5.S3.Combinatorics.Games.CrimFourPartClassification
open D5.S0.Certificates.Games.CrimGrundyRefutation

private theorem classification (a b c d : ℕ) (hba : b≤a) (hcb : c≤b) (hdc : d≤c) :
    grundy (p4 a b c d) = 0 ↔ P a b c d := by
  generalize hs : (p4 a b c d).sum = n
  induction n using Nat.strong_induction_on generalizing a b c d with
  | h n ih =>
    have ihq : ∀ e f g h : ℕ, Next a b c d e f g h →
        (grundy (p4 e f g h) = 0 ↔ P e f g h) := by
      intro e f g h hn
      have hord := next_order a b c d e f g h hba hcb hdc hn
      have hm : p4 e f g h ∈ moves (p4 a b c d) :=
        (moves_p4 a b c d _ hba hcb hdc).mpr ⟨e,f,g,h,hn,rfl⟩
      have hlt := move_decreases _ _ hm
      exact ih (p4 e f g h).sum (by omega) e f g h hord.1 hord.2.1 hord.2.2 rfl
    rw [grundy_eq]
    have hmex := mex_spec ((moves (p4 a b c d)).map grundy).toFinset
    by_cases hp : P a b c d
    · refine ⟨fun _ => hp, fun _ => ?_⟩
      by_contra hz
      have hpos : 0 < mex ((moves (p4 a b c d)).map grundy).toFinset := by
        exact Nat.zero_lt_of_ne_zero hz
      have hmem := hmex.2 0 hpos
      simp only [List.mem_toFinset,List.mem_map] at hmem
      obtain ⟨q,hq,hzero⟩ := hmem
      obtain ⟨e,f,g,h,hn,rfl⟩ := (moves_p4 a b c d q hba hcb hdc).mp hq
      exact no_P_follower a b c d e f g h hba hcb hdc hp hn ((ihq e f g h hn).mp hzero)
    · refine ⟨fun hz => ?_,fun h => False.elim (hp h)⟩
      obtain ⟨e,f,g,h,hn,hpnext⟩ := non_P_has_follower a b c d hba hcb hdc hp
      have hm : p4 e f g h ∈ moves (p4 a b c d) :=
        (moves_p4 a b c d _ hba hcb hdc).mpr ⟨e,f,g,h,hn,rfl⟩
      have hznext := (ihq e f g h hn).mpr hpnext
      have hmem : 0 ∈ ((moves (p4 a b c d)).map grundy).toFinset := by
        simp only [List.mem_toFinset,List.mem_map]
        exact ⟨p4 e f g h,hm,hznext⟩
      rw [hz] at hmex
      exact False.elim (hmex.1 hmem)
end D5.S3.Combinatorics.Games.CrimFourPartClassification

namespace D5.S3.Combinatorics.Games.CrimFourPartClassification
open D5.S0.Certificates.Games.CrimGrundyRefutation

theorem result : claim := by
  intro a b c d hd hdc hcb hba
  have he : p4 a b c d = [a,b,c,d] := by
    simp [p4,nz,show a≠0 by omega,show b≠0 by omega,show c≠0 by omega,show d≠0 by omega]
  have hclass := classification a b c d hba hcb hdc
  rw [he] at hclass
  simpa [P,four,show 0<d by omega,show a≠0 by omega,show b≠0 by omega,show c≠0 by omega,show d≠0 by omega] using hclass

end D5.S3.Combinatorics.Games.CrimFourPartClassification
