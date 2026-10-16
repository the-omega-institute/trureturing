/- GID: D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact lexicographic Boolean banks and both actual whole-row origin families. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerControllers
import D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound
import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformVariables
import D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate
import D5.S0.Computability.PreorderTreeEvaluation
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeBooleanAssignmentBanks

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open ActualImageAddressCertificate (height)
open NativeDepthPatterns (Pattern Frontier fill frontierAddress frontier_geometry)
open NativePolynomialDescriptorObstruction (fullPattern full_frontier_card)
open SparseLiteralControlTable (fullIndex full_index_address)
open NativeUniformVariables (frontier_injective)
open NativeClassRootPadding (pad)
open NativeClassRootImage (Image ImageValues OriginFiber rootType types Admissible)
open ActualCutPartitionRecovery (LiteralRow canonicalRow evaluateRow)
open NativeCutFibers (Classes LegalValues extend)
open NativeSixSourceCones (P prefix_free row filling predecessor Fiber)
open NativeRepeatedPartnerControllers
  (coord index coord_index inflate acquiredLabel type_finite_row)
open D5.S0.Computability.PreorderTreeEvaluation (word)

attribute [local instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

/-- Ordinary unfolded constructor size: every repeated occurrence is counted. -/
def size (t : Source) : Nat := (word t).length

private theorem size_mul (s t : Source) :
    size (.mul s t) = size s + size t + 1 := by
  simp [size,word]

private theorem height_mul (s t : Source) :
    height (.mul s t) = max (height s) (height t) + 1 := rfl

private theorem size_prod (s t : Source) : size (s*t) = size s + size t + 1 := size_mul s t

private theorem height_prod (s t : Source) :
    height (s*t) = max (height s) (height t) + 1 := height_mul s t

/-- The complete skeleton admits heterogeneous and repeated payloads, including
one arbitrary payload at depth zero. -/
private theorem full_fill_bounds (d : Nat) (f : Frontier (fullPattern d) → Source)
    (H M : Nat) (hh : ∀ j, height (f j) ≤ H) (hm : ∀ j, size (f j) ≤ M) :
    height (fill (fullPattern d) f) ≤ d + H ∧
    size (fill (fullPattern d) f) + 1 ≤ 2^d * (M+1) := by
  induction d with
  | zero => exact ⟨by simpa only [fullPattern,fill,Nat.zero_add] using hh (),
      by simpa [fullPattern,fill] using Nat.add_le_add_right (hm ()) 1⟩
  | succ d ih =>
      obtain ⟨hl,ml⟩ := ih (fun j => f (.inl j))
        (fun j => hh (.inl j)) (fun j => hm (.inl j))
      obtain ⟨hr,mr⟩ := ih (fun j => f (.inr j))
        (fun j => hh (.inr j)) (fun j => hm (.inr j))
      change height (.mul _ _) ≤ _ ∧ size (.mul _ _) + 1 ≤ _
      rw [height_mul,size_mul,pow_succ]
      constructor
      · exact (Nat.add_le_add_right (max_le hl hr) 1).trans (by omega)
      · nlinarith

private theorem full_fill_hom (d : Nat) (f : Frontier (fullPattern d) → Source)
    (h : Source →ₙ* Source) :
    h (fill (fullPattern d) f) = fill (fullPattern d) (h ∘ f) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [fullPattern,fill,FreeMagma.mul_eq,map_mul,ih]
      rfl

private theorem constant_full_fill (d : Nat) (t : Source) :
    fill (fullPattern d) (fun _ => t) = pad d t := by
  induction d with
  | zero => rfl
  | succ d ih =>
      change FreeMagma.mul _ _ = FreeMagma.mul _ _
      rw [ih]

private theorem pad_resources (d : Nat) (t : Source) :
    height (pad d t) = d + height t ∧
    size (pad d t) + 1 = 2^d * (size t + 1) := by
  induction d with
  | zero => simp [pad]
  | succ d ih =>
      simp only [pad,height_mul,size_mul,ih.1,max_self,pow_succ]
      constructor
      · omega
      · nlinarith [ih.2]

/-- The source markers B_j use the original native padding operation. -/
def B (j : Nat) : Source := pad j (.of false)

/-- The prescribed depth, including ell(0)=ell(1)=1. -/
def ell (n : Nat) : Nat := Nat.clog 2 (max 2 n)

private theorem ell_bounds (n : Nat) :
    0 < ell n ∧ n ≤ 2^(ell n) ∧ 2^(ell n) ≤ 4*(n+1) ∧ ell n ≤ n+1 := by
  have two : 1 < (2 : Nat) := by decide
  have hn : 1 < max 2 n := by omega
  have hp := Nat.clog_pos two hn
  have lo := Nat.le_pow_clog two (max 2 n)
  have hi : 2^(ell n-1) < max 2 n := by
    simpa only [ell,Nat.pred_eq_sub_one] using Nat.pow_pred_clog_lt_self two hn
  have step : 2^(ell n) = 2^(ell n-1)*2 := by
    rw [← pow_succ]
    congr 1
    dsimp [ell] at *
    omega
  have ln : max 2 n ≤ 2^(n+1) := by
    have lt := Nat.lt_two_pow_self (n := n+1)
    have pow2 : 2 ≤ 2^(n+1) := by
      exact (Nat.pow_le_pow_right (by decide : 1 ≤ (2:Nat)) (by omega : 1 ≤ n+1))
    omega
  have low : n ≤ 2^(ell n) := (le_max_right 2 n).trans lo
  have high : 2^(ell n) ≤ 4*(n+1) := by rw [step]; omega
  exact ⟨hp,low,high,Nat.clog_le_of_le_pow ln⟩

/-- All length-d addresses in their ordinary lexicographic order, L before R. -/
def words (d : Nat) : List Address :=
  (Finset.univ.image (frontierAddress (fullPattern d))).sort (· ≤ ·)

private theorem words_spec (d : Nat) :
    (words d).length = 2^d ∧ (words d).Nodup ∧
    (words d).Pairwise (· ≤ ·) ∧ ∀ a, a ∈ words d ↔ a.length = d := by
  refine ⟨?_,Finset.sort_nodup _ _,Finset.pairwise_sort _ _,?_⟩
  · rw [words,Finset.length_sort,
      Finset.card_image_of_injective _ (frontier_injective _),Finset.card_univ]
    exact full_frontier_card d
  · intro a
    simp only [words,Finset.mem_sort,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨j,rfl⟩; exact (frontier_geometry d _).1 j
    · intro ha; exact ⟨fullIndex d a ha,full_index_address d a ha⟩

/-- The first n words, rather than an arbitrary finite-equivalence ordering. -/
def selected (n : Nat) : List Address := (words (ell n)).take n

private theorem selected_length (n : Nat) : (selected n).length = n := by
  simp only [selected,List.length_take,(words_spec _).1]
  exact Nat.min_eq_left (ell_bounds n).2.1

/-- Zero-based Lean indices represent the source variable names 1,...,n. -/
def variableWord (n : Nat) (i : Fin n) : Address :=
  (selected n).get ⟨i.val,by rw [selected_length]; exact i.isLt⟩

def literal (n : Nat) (i : Fin n) : Address := [true,false,false] ++ variableWord n i

/-- This Boolean interpretation is total on the entire four-reply alphabet. -/
def branchBit (r : Reply) : Bool := decide (r = .branch)

/-- No height, size or witness-family premise restricts this source assignment. -/
def assignment (n : Nat) (u : Source) (i : Fin n) : Bool :=
  branchBit (readout (literal n i) (substitution u))

private theorem variable_words (n : Nat) :
    Function.Injective (variableWord n) ∧
    ∀ i, (variableWord n i).length = ell n := by
  constructor
  · intro i j hij
    have hn : (selected n).Nodup := (words_spec (ell n)).2.1.take
    have h := hn.injective_get (show (selected n).get _ = (selected n).get _ from hij)
    exact Fin.ext (congrArg (fun k : Fin (selected n).length => k.val) h)
  · intro i
    apply ((words_spec (ell n)).2.2.2 _).mp
    exact List.mem_of_mem_take (List.get_mem _ _)

/-- Every unused slot is beta, and a selected slot is B1 exactly for a true bit. -/
noncomputable def payload {n : Nat} (b : Fin n → Bool) (a : Address) : Source :=
  if ∃ i, variableWord n i = a ∧ b i = true then B 1 else .of false

noncomputable def bank {n : Nat} (b : Fin n → Bool) : Source :=
  fill (fullPattern (ell n)) (fun j => payload b (frontierAddress _ j))

private theorem payload_selected {n : Nat} (b : Fin n → Bool) (i : Fin n) :
    payload b (variableWord n i) = if b i then B 1 else .of false := by
  have eq : (∃ j, variableWord n j = variableWord n i ∧ b j = true) ↔ b i = true := by
    constructor
    · rintro ⟨j,hj,hb⟩; exact (variable_words n).1 hj ▸ hb
    · intro hb; exact ⟨i,rfl,hb⟩
  simp only [payload,eq]

private theorem bank_recover {n : Nat} (b : Fin n → Bool) (a : Address)
    (ha : a.length = ell n) : subtree a (bank b) = some (payload b a) := by
  have hit := (frontier_geometry (ell n) _).2.1
    (fun j => payload b (frontierAddress _ j)) (fullIndex (ell n) a ha)
  simpa only [bank,full_index_address] using hit

private theorem bank_resources {n : Nat} (b : Fin n → Bool) :
    height (bank b) ≤ ell n + 1 ∧ size (bank b) + 1 ≤ 4 * 2^(ell n) := by
  have small (a : Address) : height (payload b a) ≤ 1 ∧ size (payload b a) ≤ 3 := by
    unfold payload
    split_ifs <;> decide
  have bnd := full_fill_bounds (ell n)
    (fun j => payload b (frontierAddress _ j)) 1 3
    (fun j => (small _).1) (fun j => (small _).2)
  exact ⟨bnd.1,by simpa [bank,Nat.mul_comm] using bnd.2⟩

theorem B_height (d : Nat) : height (B d) = d := by
  simpa [B,height,GenealogicalFiberTransport.decompose,BinaryTree.height]
    using (pad_resources d (.of false)).1

private theorem B_size (d : Nat) : size (B d) + 1 = 2^d * 2 :=
  (pad_resources d (.of false)).2

private theorem bank_branch {n : Nat} (b : Fin n → Bool) :
    ∃ l r, bank b = .mul l r := by
  have hp := (ell_bounds n).1
  unfold bank
  cases he : ell n with
  | zero => omega
  | succ d => exact ⟨_,_,rfl⟩

private theorem bank_positive {n : Nat} (b : Fin n → Bool) : 0 < height (bank b) := by
  obtain ⟨l,r,h⟩ := bank_branch b
  rw [h,height_mul]
  omega

private theorem B_branch (d : Nat) (hd : 0 < d) : rootType (B d) = none := by
  cases d with
  | zero => omega
  | succ d => rfl

noncomputable def prePayload {n : Nat} (b : Fin n → Bool) (a : Address) : Source :=
  if ∃ i, variableWord n i = a ∧ b i = true
  then .mul (.of true) (.of true) else .of true

noncomputable def preBank {n : Nat} (b : Fin n → Bool) : Source :=
  fill (fullPattern (ell n)) (fun j => prePayload b (frontierAddress _ j))

private theorem bank_image {n : Nat} (b : Fin n → Bool) :
    substitution (preBank b) = bank b := by
  rw [preBank,full_fill_hom]
  unfold bank
  congr 1
  funext j
  change substitution (prePayload b _) = payload b _
  unfold prePayload payload
  split_ifs <;> rfl

private theorem pre_bank_resources {n : Nat} (b : Fin n → Bool) :
    height (preBank b) ≤ ell n + 1 ∧ size (preBank b) + 1 ≤ 4 * 2^(ell n) := by
  have small (a : Address) : height (prePayload b a) ≤ 1 ∧ size (prePayload b a) ≤ 3 := by
    unfold prePayload
    split_ifs <;> decide
  have bnd := full_fill_bounds (ell n)
    (fun j => prePayload b (frontierAddress _ j)) 1 3
    (fun j => (small _).1) (fun j => (small _).2)
  exact ⟨bnd.1,by simpa [preBank,Nat.mul_comm] using bnd.2⟩

theorem pad_preimage (d : Nat) :
    substitution (pad d (.of true)) = B d := by
  rw [← constant_full_fill d (.of true),full_fill_hom]
  exact constant_full_fill d (.of false)

/-- The two literal source tuples, in native order (a,b1,b2,c,b3,b4). -/
def tuple (n : Nat) (C : Source) (second : Bool) : Fin 6 → Source :=
  ![.of false, if second then B (ell n+2) else .of true,
    if second then .of true else B (ell n+2), C, B (ell n+3), B (ell n+4)]

/-- The actual predecessor retains the exceptional beta block in its original
position and repeats the one inverse bank value at both c occurrences. -/
noncomputable def origin {n : Nat} (b : Fin n → Bool) (second : Bool) : Source :=
  .mul (.mul (if second then .mul (.of true) (pad (ell n+2) (.of true)) else .of false)
              (if second then .of false else .mul (.of true) (pad (ell n+2) (.of true))))
       (.mul (.mul (preBank b) (pad (ell n+3) (.of true)))
             (.mul (preBank b) (pad (ell n+4) (.of true))))

def targetIndex (second : Bool) : Fin 5 := if second then 2 else 1

private theorem origin_image {n : Nat} (b : Fin n → Bool) (second : Bool) :
    substitution (origin b second) = filling (tuple n (bank b) second) := by
  cases second <;>
    simp only [origin,tuple,filling,Bool.false_eq_true,if_false,if_true,
      FreeMagma.mul_eq,map_mul,pad_preimage,bank_image] <;> rfl

private theorem tuple_distinct {n : Nat} (b : Fin n → Bool) (second : Bool) :
    Function.Injective (tuple n (bank b) second) := by
  have hb := (bank_resources b).1
  have hp := bank_positive b
  intro i j h
  have heights := congrArg height h
  cases second <;> fin_cases i <;> fin_cases j <;> try rfl
  all_goals
    exfalso
    have roots := congrArg rootType h
    simp [tuple,show rootType (.of true) = some true from rfl,
      show rootType (.of false) = some false from rfl] at roots <;>
      simp [tuple,B_height,show height (.of true) = 0 from rfl,
        show height (.of false) = 0 from rfl] at heights <;> omega

private theorem whole_row_of_values (x : Fin 6 → Source) (u : Source)
    (distinct : Function.Injective x) (image : substitution u = filling x) :
    canonicalRow P (substitution u) = row ∧
    canonicalRow P u = predecessor (acquiredLabel (fun i => rootType (x i))) := by
  let values : Classes row → Source := fun d => x (index d)
  have vi : Function.Injective values := by
    intro d e h
    have eq : index d = index e := distinct h
    exact (coord_index d).symm.trans ((congrArg coord eq).trans (coord_index e))
  have evaluation : evaluateRow (extend row values) row = filling x := by
    simp [row,evaluateRow,extend,NativeCutFibers.labels,index,values,filling]
  have ref : canonicalRow P (NativeSixSourceCones.current 0) = row :=
    (NativeSixSourceCones.six_source_realization.1 0).2.1
  have preserve : ∀ v : LegalValues row,
      canonicalRow P (evaluateRow (extend row v.val) row) = row := by
    rw [← ref]
    exact NativeCutFibers.legal_values_row P prefix_free (NativeSixSourceCones.current 0)
  have currentRow : canonicalRow P (substitution u) = row := by
    rw [image,← evaluation]
    exact preserve ⟨values,vi⟩
  let v : ImageValues row := ⟨⟨values,vi⟩,⟨u,image.trans evaluation.symm⟩⟩
  let actual : Fiber := ⟨u,currentRow⟩
  have refOrigin : canonicalRow P (substitution (NativeSixSourceCones.origin 0)) = row := by
    rw [(NativeSixSourceCones.six_source_realization.1 0).1]
    exact ref
  have admissible : ∀ v : ImageValues row, Admissible row (types row v.val.val) := by
    rw [← ref]
    exact NativeFullRootFeasibility.actual_type P prefix_free (NativeSixSourceCones.current 0)
  have bridge := (NativeFullRootFeasibility.native_full_root_feasibility
    P prefix_free (NativeSixSourceCones.origin 0) 1 0 (by decide)).1
  rw [refOrigin] at bridge
  have target := (bridge v actual (image.trans evaluation.symm)).2.2
  have type_eq : inflate (fun i => rootType (x i)) = types row v.val.val := rfl
  have computed := NativeFiniteRootMinimax.finite_root_minimax row []
  have finite := type_finite_row (fun i => rootType (x i))
    (by rw [type_eq]; exact admissible v)
  refine ⟨currentRow,?_⟩
  exact target.symm.trans ((computed.2.2.2.2.2 _).symm.trans (by rwa [← type_eq]))

private theorem tuple_label {n : Nat} (b : Fin n → Bool) (second : Bool) :
    acquiredLabel (fun i => rootType (tuple n (bank b) second i)) = targetIndex second := by
  have hb := B_branch (ell n+2) (by omega)
  cases second <;>
    simp [acquiredLabel,targetIndex,tuple,hb,show rootType (.of true) = some true from rfl]

private theorem origin_rows {n : Nat} (b : Fin n → Bool) (second : Bool) :
    canonicalRow P (substitution (origin b second)) = row ∧
    canonicalRow P (origin b second) = predecessor (targetIndex second) := by
  simpa only [tuple_label] using
    whole_row_of_values (tuple n (bank b) second) (origin b second)
      (tuple_distinct b second) (origin_image b second)

private theorem literal_subtree {n : Nat} (b : Fin n → Bool) (second : Bool) (i : Fin n) :
    subtree (literal n i) (substitution (origin b second)) =
      some (if b i then B 1 else .of false) := by
  rw [origin_image]
  change subtree (variableWord n i) (bank b) = _
  rw [bank_recover b _ ((variable_words n).2 i),payload_selected]

private theorem origin_assignment {n : Nat} (b : Fin n → Bool) (second : Bool) :
    assignment n (origin b second) = b := by
  funext i
  have atRoot := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (literal n i) [] (substitution (origin b second))
  rw [List.append_nil,literal_subtree] at atRoot
  have bit := congrArg branchBit atRoot
  cases hb : b i <;> simpa [assignment,branchBit,hb,readout,B,pad] using bit

private theorem witness_resources {n : Nat} (b : Fin n → Bool) (second : Bool) :
    height (filling (tuple n (bank b) second)) ≤ ell n+7 ∧
    size (filling (tuple n (bank b) second)) + 1 ≤ 280*(n+1) ∧
    height (origin b second) ≤ ell n+7 ∧ size (origin b second) + 1 ≤ 280*(n+1) := by
  have hb := bank_resources b
  have hp := pre_bank_resources b
  have marker (k : Nat) :
      height (pad (ell n+k) (.of true)) = ell n+k ∧
      size (pad (ell n+k) (.of true)) + 1 = 2^(ell n+k)*2 := by
    simpa [height,GenealogicalFiberTransport.decompose,BinaryTree.height,size,word]
      using pad_resources (ell n+k) (.of true)
  have qpos : 0 < 2^(ell n) := by positivity
  have qbound := (ell_bounds n).2.2.1
  have markers := And.intro (B_size (ell n+2))
    (And.intro (B_size (ell n+3)) (B_size (ell n+4)))
  have inverseMarkers := And.intro (marker 2) (And.intro (marker 3) (marker 4))
  cases second <;>
    simp [tuple,filling,origin,
      height_prod,size_prod,B_height,show height (.of true) = 0 from rfl,
      show height (.of false) = 0 from rfl,show size (.of true) = 1 from rfl,
      show size (.of false) = 1 from rfl]
  all_goals
    simp only [pow_add] at markers inverseMarkers
    norm_num at markers inverseMarkers
    rcases inverseMarkers with ⟨m2,m3,m4⟩
    simp only [m2.1,m3.1,m4.1] at *
    omega

/-- The unconditional Zstar tuple is B1,...,B6 in D order, transported to
native order (a,b1,b2,c,b3,b4). -/
def zeroTuple : Fin 6 → Source := ![B 1,B 3,B 4,B 2,B 5,B 6]

def zeroOrigin : Source := filling ![pad 1 (.of true),pad 3 (.of true),pad 4 (.of true),
  pad 2 (.of true),pad 5 (.of true),pad 6 (.of true)]

private theorem zero_witness :
    Function.Injective zeroTuple ∧ substitution zeroOrigin = filling zeroTuple ∧
    canonicalRow P (substitution zeroOrigin) = row ∧ canonicalRow P zeroOrigin = predecessor 0 := by
  have distinct : Function.Injective zeroTuple := by decide +kernel
  have image : substitution zeroOrigin = filling zeroTuple := by decide +kernel
  have labels : acquiredLabel (fun i => rootType (zeroTuple i)) = 0 := by decide +kernel
  have rows := whole_row_of_values zeroTuple zeroOrigin distinct image
  exact ⟨distinct,image,by simpa only [labels] using rows⟩

/-- Names are finite syntactic words. Deduplication fixes one syntactic order
separately for each formula's occurrence list. -/
abbrev Name := List Bool

def localCount (names : List Name) : Nat := names.dedup.length

abbrev Appearing (names : List Name) := {a : Name // a ∈ names}

def localIndex (names : List Name) (a : Appearing names) : Fin (localCount names) :=
  ⟨names.dedup.idxOf a.val,List.idxOf_lt_length_iff.mpr (List.mem_dedup.mpr a.property)⟩

/-- The common universe uses the largest local count, not the union of names. -/
def commonCount (formulas : List (List Name)) : Nat :=
  max 1 ((formulas.map localCount).foldr max 0)

private theorem local_bound (formulas : List (List Name)) (names : List Name)
    (mem : names ∈ formulas) : localCount names ≤ commonCount formulas := by
  exact (List.le_max_of_le (List.mem_map.mpr ⟨names,mem,rfl⟩) le_rfl).trans
    (le_max_right _ _)

def commonIndex (formulas : List (List Name)) (names : List Name) (mem : names ∈ formulas)
    (a : Appearing names) : Fin (commonCount formulas) :=
  (localIndex names a).castLE (local_bound formulas names mem)

private theorem local_index_injective (names : List Name) :
    Function.Injective (localIndex names) := by
  intro a b h
  apply Subtype.ext
  exact (List.idxOf_inj (List.mem_dedup.mpr a.property)).mp (congrArg Fin.val h)

/-- Each formula may extend its own arbitrary assignment into the common
universe independently. No simultaneous agreement between different formulas
is imposed. -/
def LocalRenumbering : Prop :=
  ∀ formulas : List (List Name), 1 ≤ commonCount formulas ∧
    ∀ (names : List Name) (mem : names ∈ formulas),
      localCount names ≤ commonCount formulas ∧
      Function.Injective (commonIndex formulas names mem) ∧
      ∀ a : Appearing names → Bool, ∃ b : Fin (commonCount formulas) → Bool,
        ∀ x, b (commonIndex formulas names mem x) = a x

private theorem local_renumbering : LocalRenumbering := by
  intro formulas
  refine ⟨le_max_left _ _,?_⟩
  intro names mem
  have inj : Function.Injective (commonIndex formulas names mem) := by
    intro a b h
    apply local_index_injective names
    apply Fin.ext
    exact congrArg (fun i : Fin (commonCount formulas) => i.val) h
  refine ⟨local_bound formulas names mem,inj,?_⟩
  intro a
  exact ⟨Function.extend (commonIndex formulas names mem) a (fun _ => false),
    inj.extend_apply a (fun _ => false)⟩

/-- Complete fixed literal data with explicit polynomial total length. -/
def LiteralSpec (n : Nat) : Prop :=
  (words (ell n)).Pairwise (· ≤ ·) ∧
  (∀ a, a ∈ words (ell n) ↔ a.length = ell n) ∧
  (selected n).length = n ∧ (selected n).Nodup ∧
  Function.Injective (variableWord n) ∧
  (∀ i, (variableWord n i).length = ell n ∧
    literal n i = [true,false,false] ++ variableWord n i ∧
    (literal n i).length = ell n+3) ∧
  (List.ofFn (fun i : Fin n => (literal n i).length)).sum = n*(ell n+3) ∧
  (List.ofFn (fun i : Fin n => (literal n i).length)).sum ≤ n*(n+4)

private theorem literal_spec (n : Nat) : LiteralSpec n := by
  have length (i : Fin n) : (literal n i).length = ell n+3 := by
    simp [literal,(variable_words n).2 i]
  have total : (List.ofFn (fun i : Fin n => (literal n i).length)).sum = n*(ell n+3) := by
    simp_rw [length]
    simp
  refine ⟨(words_spec _).2.2.1,(words_spec _).2.2.2,selected_length n,
    (words_spec _).2.1.take,(variable_words n).1,
    fun i => ⟨(variable_words n).2 i,rfl,length i⟩,total,?_⟩
  rw [total]
  exact Nat.mul_le_mul_left n (by have h := (ell_bounds n).2.2.2; omega)

/-- The same stationary literal has the same Boolean interpretation for every
finite source, without any resource or profile premise. -/
def AllSources (n : Nat) : Prop :=
  (∀ (u : Source) (i : Fin n), assignment n u i = true ↔
    readout (literal n i) (substitution u) = .branch) ∧
  (∀ (u : Source) (i j : Fin n), literal n i = literal n j → assignment n u i = assignment n u j) ∧
  branchBit .branch = true ∧ branchBit .alpha = false ∧
  branchBit .beta = false ∧ branchBit .absent = false

private theorem all_sources (n : Nat) : AllSources n := by
  refine ⟨by intro u i; simp [assignment,branchBit],?_,rfl,rfl,rfl,rfl⟩
  intro u i j h
  simp only [assignment,h]

/-- All frontier words, including unused words, have their specified whole
subtree. Size is ordinary unfolded constructor size. -/
def BankSpec (n : Nat) (b : Fin n → Bool) (C : Source) : Prop :=
  C = fill (fullPattern (ell n)) (fun j => payload b (frontierAddress _ j)) ∧
  (∀ a, a.length = ell n → subtree a C = some (payload b a)) ∧
  (∀ i, payload b (variableWord n i) = if b i then B 1 else .of false) ∧
  (∀ a, (∀ i, variableWord n i ≠ a) → payload b a = .of false) ∧
  Image C ∧ rootType C = none ∧ height C ≤ ell n+1 ∧ size C+1 ≤ 16*(n+1)

private theorem bank_spec {n : Nat} (b : Fin n → Bool) : BankSpec n b (bank b) := by
  have bounds := bank_resources b
  obtain ⟨l,r,branch⟩ := bank_branch b
  refine ⟨rfl,bank_recover b,payload_selected b,?_,⟨preBank b,bank_image b⟩,
    by rw [branch]; rfl,bounds.1,?_⟩
  · intro a unused
    apply if_neg
    rintro ⟨i,hi,_⟩
    exact unused i hi
  · have hq := (ell_bounds n).2.2.1
    omega

/-- Whole current tree, all fifteen whole-value inequalities, complete target,
exact literal subtrees, and bounds for both actual origin and current image. -/
def WitnessSpec (n : Nat) (b : Fin n → Bool) (C : Source) (second : Bool) (u : Fiber) : Prop :=
  substitution u.val = filling (tuple n C second) ∧
  Function.Injective (tuple n C second) ∧
  canonicalRow P u.val = predecessor (targetIndex second) ∧
  assignment n u.val = b ∧
  (∀ i, subtree (literal n i) (substitution u.val) =
    some (if b i then B 1 else .of false)) ∧
  height (substitution u.val) ≤ ell n+7 ∧ size (substitution u.val)+1 ≤ 280*(n+1) ∧
  height u.val ≤ ell n+7 ∧ size u.val+1 ≤ 280*(n+1)

private theorem witness_spec {n : Nat} (b : Fin n → Bool) (second : Bool) :
    ∃ u : Fiber, WitnessSpec n b (bank b) second u := by
  let u : Fiber := ⟨origin b second,(origin_rows b second).1⟩
  refine ⟨u,origin_image b second,tuple_distinct b second,(origin_rows b second).2,
    origin_assignment b second,literal_subtree b second,?_⟩
  change height (substitution (origin b second)) ≤ _ ∧ _
  rw [origin_image]
  exact witness_resources b second

/-- Source D coordinates select these native coordinates. -/
def dToNative : Fin 6 → Fin 6 := ![0,3,1,2,4,5]

/-- The inverse permutation selects D coordinates in native order. -/
def nativeToD : Fin 6 → Fin 6 := ![0,2,3,1,4,5]

def CoordinateSpec : Prop :=
  Function.LeftInverse dToNative nativeToD ∧
  Function.LeftInverse nativeToD dToNative ∧
  (fun i : Fin 6 => (coord i).val) = ![0,1,3,4,5,7]

private theorem coordinate_spec : CoordinateSpec := by
  refine ⟨?_,?_,?_⟩
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-- The full Boolean-bank statement, with its all-source and existential
clauses kept separate. The two witnesses exist also at n=0. -/
def Lemma61 (C : (n : Nat) → (Fin n → Bool) → Source) : Prop :=
  (∀ n, LiteralSpec n ∧ AllSources n ∧
    ∀ b : Fin n → Bool, BankSpec n b (C n b) ∧
      ∀ second : Bool, ∃ u : Fiber, WitnessSpec n b (C n b) second u) ∧
  (ell 0 = 1 ∧ selected 0 = [] ∧ ∀ b : Fin 0 → Bool, C 0 b = B 1) ∧
  (∃ u : Fiber, substitution u.val = filling zeroTuple ∧ Function.Injective zeroTuple ∧
    canonicalRow P u.val = predecessor 0) ∧
  LocalRenumbering ∧ CoordinateSpec

/-- Every assignment has both prescribed actual origins and full predecessor
rows; the fixed lexicographic literals define a total assignment on all sources. -/
theorem native_boolean_assignment_banks : Lemma61 (fun n b => @bank n b) := by
  refine ⟨?_,?_,?_,local_renumbering,coordinate_spec⟩
  · intro n
    exact ⟨literal_spec n,all_sources n,fun b => ⟨bank_spec b,witness_spec b⟩⟩
  · refine ⟨by decide,rfl,?_⟩
    intro b
    change @bank 0 b = B 1
    unfold bank
    rw [show ell 0 = 1 from by decide]
    simp [payload,fullPattern,fill,B,pad]
  · exact ⟨⟨zeroOrigin,zero_witness.2.2.1⟩,zero_witness.2.1,zero_witness.1,zero_witness.2.2.2⟩

#print axioms native_boolean_assignment_banks

end D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeBooleanAssignmentBanks
