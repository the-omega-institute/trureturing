/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.wordFour; instance=D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.wordFour
   digest: Exact integer continuation polynomials certified by their compatible successors. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers

/-! A sparse transfer step sums only allowed successor words. Horner evaluation
checks the source vector polynomial in the full state space. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinTransferCertificates

open HardinActualTransfers
open HardinColumnContinuations (Column cross columnV)
open HardinThinGraphTransport (Row proper compatible)
open private sum_words cross_iff from
  D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers

private def columnBond {n : ℕ} (i j : Fin n) : Prop :=
  i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1

private def wordBond {n : ℕ} (d : Bool) (i j : Fin n) : Prop :=
  if d then i.val + 1 = j.val ∨ j.val + 1 = i.val else i = j

private instance {n : ℕ} : DecidableRel (@columnBond n) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

private instance {n : ℕ} (d : Bool) : DecidableRel (@wordBond n d) :=
  fun i j => by unfold wordBond; infer_instance

private theorem columnBond_spec {h : ℕ} (p q : Column h) :
    (∀ i j, columnBond i j → p i ≠ q j) ↔ cross p q := (cross_iff p q).symm

private theorem wordBond_spec {k : ℕ} (d : Bool) (p q : Row k) :
    (∀ i j, wordBond d i j → p i ≠ q j) ↔ compatible d p q := by
  cases d
  · simp only [wordBond, compatible, Bool.false_eq_true, ite_false]
    exact ⟨fun h i => h i i rfl, fun h i j hij => hij ▸ h i⟩
  · simp only [wordBond, compatible, ite_true]
    constructor
    · intro h a
      exact ⟨h a.castSucc a.succ (Or.inl rfl), h a.succ a.castSucc (Or.inr rfl)⟩
    · intro h i j hij
      rcases hij with hij | hij
      · let a : Fin k := ⟨i.val, by omega⟩
        have hi : i = a.castSucc := Fin.ext rfl
        have hj : j = a.succ := Fin.ext hij.symm
        rw [hi, hj]
        exact (h a).1
      · let a : Fin k := ⟨j.val, by omega⟩
        have hi : i = a.succ := Fin.ext hij.symm
        have hj : j = a.castSucc := Fin.ext rfl
        rw [hi, hj]
        exact (h a).2

private def candidates {n : ℕ} (bond : Fin n → Fin n → Prop) [DecidableRel bond]
    (p : Fin n → Fin 3) : Finset (Fin n → Fin 3) :=
  Fintype.piFinset fun j => Finset.univ.filter fun c => ∀ i, bond i j → p i ≠ c

private theorem mem_candidates {n : ℕ} (bond : Fin n → Fin n → Prop) [DecidableRel bond]
    (p q : Fin n → Fin 3) : q ∈ candidates bond p ↔ ∀ i j, bond i j → p i ≠ q j := by
  simp only [candidates, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h i j => h j i, fun h j i => h i j⟩

private def code (n : ℕ) : (Fin n → Fin 3) ≃ Fin (3 ^ n) := finFunctionFinEquiv

private def columnSuccessors (h : ℕ) (a : Fin (3 ^ (h + 1))) : Finset (Fin (3 ^ (h + 1))) :=
  (candidates columnBond ((code (h + 1)).symm a)).map (code (h + 1)).toEmbedding

private def wordSuccessors (d : Bool) (k : ℕ) (a : Fin (3 ^ (k + 1))) :
    Finset (Fin (3 ^ (k + 1))) :=
  let p := (code (k + 1)).symm a
  if proper p then
    ((candidates (wordBond d) p).filter proper).map (code (k + 1)).toEmbedding
  else ∅

private theorem column_action (h : ℕ) (p : Column h) (v : Fin (3 ^ (h + 1)) → ℤ) :
    (∑ j ∈ columnSuccessors h (code (h + 1) p), v j) =
      (C h).mulVec (fun q => v (code (h + 1) q)) p := by
  simp only [columnSuccessors, Equiv.symm_apply_apply, Finset.sum_map, Equiv.toEmbedding_apply]
  have hc : candidates columnBond p = Finset.univ.filter (cross p) := by
    ext x
    simp [mem_candidates, columnBond_spec]
  rw [hc, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  change (if cross p q then v (code (h + 1) q) else 0) =
    (if cross p q then 1 else 0) * v (code (h + 1) q)
  split_ifs <;> simp

private theorem word_action (d : Bool) (k : ℕ) (p : Word k) (v : Fin (3 ^ (k + 1)) → ℤ) :
    (∑ j ∈ wordSuccessors d k (code (k + 1) p.val), v j) =
      (wordTransfer d k).mulVec (fun q => v (code (k + 1) q.val)) p := by
  simp only [wordSuccessors, Equiv.symm_apply_apply, p.property, ite_true,
    Finset.sum_map, Equiv.toEmbedding_apply]
  have hc : (candidates (wordBond d) p.val).filter proper =
      Finset.univ.filter (fun q => proper q ∧ compatible d p.val q) := by
    ext x
    simp [mem_candidates, wordBond_spec, and_comm]
  rw [hc, Finset.sum_filter]
  change _ = ∑ q : Word k, (if compatible d p.val q.val then 1 else 0) * v (code (k + 1) q.val)
  rw [sum_words (fun q => (if compatible d p.val q then 1 else 0) * v (code (k + 1) q))]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hp : proper q <;> by_cases hb : compatible d p.val q <;> simp [hp, hb]

private def step {N : ℕ} (edges : Vector (Finset (Fin N)) N) (v : Vector ℤ N) :
    Vector ℤ N :=
  Vector.ofFn fun i => ∑ j ∈ edges[i.val], v[j.val]

private def residual {N : ℕ} (edges : Vector (Finset (Fin N)) N) (initial : Vector ℤ N) :
    {d : ℕ} → (Fin d → ℤ) → Vector ℤ N
  | 0, _ => initial
  | d + 1, c =>
    let v := step edges (residual edges initial (fun i : Fin d => c i.castSucc))
    Vector.ofFn fun i => v[i.val] - c (Fin.last d) * initial[i.val]

private theorem residual_value {A : Type} [Fintype A] [DecidableEq A] {N : ℕ}
    (T : Matrix A A ℤ) (encode : A → Fin N)
    (edges : Vector (Finset (Fin N)) N)
    (action : ∀ (a : A) (w : Fin N → ℤ),
      (∑ j ∈ edges[(encode a).val], w j) = T.mulVec (fun q => w (encode q)) a)
    (initial : Vector ℤ N) (b : ℕ)
    (init : ∀ a, initial[(encode a).val] = (T ^ b).mulVec (1 : A → ℤ) a)
    {d : ℕ} (c : Fin d → ℤ) (a : A) :
    (residual edges initial c)[(encode a).val] =
      (T ^ (b + d)).mulVec (1 : A → ℤ) a -
        (∑ j : Fin d, c j • (T ^ (b + d - (j.val + 1))).mulVec (1 : A → ℤ)) a := by
  induction d generalizing a with
  | zero => simpa [residual] using init a
  | succ d ih =>
    simp only [residual, Vector.getElem_ofFn, step, init]
    rw [action a (fun j => (residual edges initial (fun i : Fin d => c i.castSucc))[j.val])]
    have hv : (fun a : A =>
      (residual edges initial (fun i : Fin d => c i.castSucc))[(encode a).val]) =
        (T ^ (b + d)).mulVec (1 : A → ℤ) - ∑ i : Fin d,
          c i.castSucc • (T ^ (b + d - (i.val + 1))).mulVec (1 : A → ℤ) :=
      funext (ih (fun i : Fin d => c i.castSucc))
    rw [hv, Matrix.mulVec_sub, Matrix.mulVec_sum]
    have advance (m : ℕ) : T * T ^ m = T ^ (m + 1) := (pow_succ' T m).symm
    simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, advance,
      Fin.sum_univ_castSucc, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply, Fin.val_castSucc, Fin.val_last]
    have hlast : b + (d + 1) - (d + 1) = b := by omega
    have hl (i : Fin d) : (b + d - (i.val + 1)) + 1 = b + (d + 1) - (i.val + 1) := by
      have hi := i.isLt
      omega
    simp only [hlast, hl]
    change _ - _ - _ = _ - (_ + _)
    ring

private theorem check_residual {A : Type} [Fintype A] [DecidableEq A] {N : ℕ}
    (T : Matrix A A ℤ) (encode : A → Fin N)
    (edges : Vector (Finset (Fin N)) N)
    (action : ∀ (a : A) (w : Fin N → ℤ),
      (∑ j ∈ edges[(encode a).val], w j) = T.mulVec (fun q => w (encode q)) a)
    (initial : Vector ℤ N) (b : ℕ)
    (init : ∀ a, initial[(encode a).val] = (T ^ b).mulVec (1 : A → ℤ) a)
    {d : ℕ} (c : Fin d → ℤ) (res : residual edges initial c = Vector.replicate N 0) :
    IsLagRelation T b c := by
  funext a
  have h := residual_value T encode edges action initial b init c a
  rw [res, Vector.getElem_replicate] at h
  exact sub_eq_zero.mp h.symm

private def wordEdges (d : Bool) (k : ℕ) := Vector.ofFn (wordSuccessors d k)

private def wordStart (k : ℕ) : Vector ℤ (3 ^ (k + 1)) :=
  Vector.ofFn fun a => if proper ((code (k + 1)).symm a) then 1 else 0

private theorem check_words (d : Bool) (k : ℕ) {r : ℕ} (c : Fin r → ℤ)
    (res : residual (wordEdges d k) (wordStart k) c = Vector.replicate (3 ^ (k + 1)) 0) :
    IsLagRelation (wordTransfer d k) 0 c := by
  apply check_residual (wordTransfer d k) (fun p => code (k + 1) p.val)
    (wordEdges d k) _ _ 0 _ c res
  · intro p v
    simpa [wordEdges] using word_action d k p v
  · intro p
    simp [wordStart, p.property]

/-- The degree-two relation already holds at shift zero on all one-row columns. -/
theorem rowOne :
    IsLagRelation (C 0) 0 ![3, -2] ∧
    (∑ j : Fin 2, (![3, -2] : Fin 2 → ℤ) j) = 1 := by
  refine ⟨?_, by decide⟩
  have values : ∀ p : Column 0, columnV 1 p = 2 ∧ columnV 2 p = 4 := by
    decide +kernel
  have step (p : Column 0) : (C 0).mulVec (1 : Column 0 → ℤ) p = (columnV 1 p : ℤ) := by
    simpa only [pow_one] using column_power 0 1 p
  unfold IsLagRelation
  funext p
  have initial : columnV 0 p = 1 := rfl
  norm_num [Fin.sum_univ_succ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    column_power, step, initial, (values p).1, (values p).2]

/-- Source degree-3 coefficient list for the proper-word transfer. -/
def wordFourCoefficients : Fin 3 → ℤ :=
  ![8, -11, 4]
/-- Source polynomial of degree 3 with no initial shift. -/
theorem wordFour :
    IsLagRelation (wordTransfer true 3) 0 wordFourCoefficients ∧
    (∑ j, wordFourCoefficients j) = 1 := by
  exact ⟨check_words true 3 _ (by decide +kernel), by decide⟩

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinTransferCertificates
