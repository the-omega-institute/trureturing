/- GID: D5/S3/ConceptDynamics/Coding/FixedPositivePartitionSseDistance
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FixedPositivePartitionSseDistance
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Fixed positive group-ring partition matrices have exact rectangular exchange distance. -/

import D5.S3.Combinatorics.Partitions.PartitionLInftyGeodesic
import D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
import D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy
import D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Coding.FixedPositivePartitionSseDistance

open D5.S3.Combinatorics.Partitions.PartitionLInftyGeodesic
open D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy
open D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
open scoped BigOperators

noncomputable section
universe u

/-- The upper Jordan shift, including empty blocks. -/
def jordanShift (a : ℕ) : Mat ℕ a a :=
  fun i j => if i.val + 1 = j.val then 1 else 0

/-- Prefix-sum coordinates depend on the partition alone. -/
def blockCoordinates {n : ℕ} (p : Partition n) :
    (Σ i : Fin n, Fin (coord p i)) ≃ Fin n := by
  have hlist : List.ofFn (coord p) = p.val := by
    apply List.ext_get
    · simp [p.property.1]
    · intro i hi hj
      simp [coord]
  have hsum : ∑ i, coord p i = n := by
    rw [← List.sum_ofFn, hlist]
    exact p.property.2.2
  exact finSigmaFinEquiv.trans (finCongr hsum)

/-- The endpoint shift in its fixed prefix-sum coordinates. -/
def partitionShift {n : ℕ} (p : Partition n) : Mat ℕ n n :=
  Matrix.reindex (blockCoordinates p) (blockCoordinates p)
    (Matrix.blockDiagonal' fun i => jordanShift (coord p i))

/-- The fixed natural group-ring endpoint with baseline |H| cubed times n. -/
def partitionMatrix (H : Type u) [Group H] [Fintype H]
    {n : ℕ} (p : Partition n) : Mat (MonoidAlgebra ℕ H) n n :=
  fun i j => toNat ((Fintype.card H ^ 3 * n : ℕ) • uniform H +
    (Fintype.card H * partitionShift p i j) •
      ((Fintype.card H : ℕ) • (1 : MonoidAlgebra ℤ H) - uniform H))


set_option maxHeartbeats 1800000 in
-- The proof elaborates cumulative quotients and dependent block coordinates locally.
/-- The fixed positive partition family attains its maximum-coordinate distance,
and every rectangular exchange chain has at least that length. -/
theorem theorem32_2 (H : Type u) [Group H] [Fintype H] [Nontrivial H]
    {n : ℕ} (hn : 1 ≤ n) (p r : Partition n) :
    Nonempty (ExchangeChain (MonoidAlgebra ℕ H)
      (partitionMatrix H p) (partitionMatrix H r) (dInf p r)) ∧
    ∀ L : ℕ, ExchangeChain (MonoidAlgebra ℕ H)
      (partitionMatrix H p) (partitionMatrix H r) L → dInf p r ≤ L := by
  classical
  have quotient_layer {V W : Type u} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
      (T : Module.End ℚ V) (Q : Module.End ℚ W)
      (R : W →ₗ[ℚ] V) (S : V →ₗ[ℚ] W) (L : ℕ)
      (hTR : T.comp R = R.comp Q) (hQS : Q.comp S = S.comp T)
      (hRS : R.comp S = T ^ L) :
      ∀ j : ℕ,
        Module.finrank ℚ (LinearMap.range (T ^ (j + L))) -
          Module.finrank ℚ (LinearMap.range (T ^ (j + L + 1))) ≤
        Module.finrank ℚ (LinearMap.range (Q ^ j)) -
          Module.finrank ℚ (LinearMap.range (Q ^ (j + 1))) := by
    classical
    intro j
    have hp (k : ℕ) : (Q ^ k).comp S = S.comp (T ^ k) := by
      induction k with
      | zero => ext x; simp
      | succ k ih =>
          rw [pow_succ', pow_succ', Module.End.mul_eq_comp, Module.End.mul_eq_comp,
            LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc, hQS]
          simp only [LinearMap.comp_assoc]
    have invrange {E : Type u} [AddCommGroup E] [Module ℚ E]
        (f : Module.End ℚ E) (k : ℕ) :
        ∀ x ∈ LinearMap.range (f ^ k), f x ∈ LinearMap.range (f ^ k) := by
      rintro _ ⟨x, rfl⟩
      refine ⟨f x, ?_⟩
      exact congrArg (fun z : Module.End ℚ E => z x) (Commute.self_pow f k).eq.symm
    let I := LinearMap.range (T ^ j)
    let M := I.map S
    let N := LinearMap.range (T ^ (j + L))
    let J := LinearMap.range (Q ^ j)
    have hMJ : M ≤ J := by
      rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
      exact ⟨S y, congrArg (fun f : V →ₗ[ℚ] W => f y) (hp j)⟩
    have hM (x : M) : Q x.val ∈ M := by
      obtain ⟨y, hy, hxy⟩ := x.property
      refine ⟨T y, invrange T j y hy, ?_⟩
      rw [← hxy]
      exact (congrArg (fun f : V →ₗ[ℚ] W => f y) hQS).symm
    have hN (x : N) : T x.val ∈ N := invrange T (j + L) x.val x.property
    have hRM : M.map R = N := by
      rw [← Submodule.map_comp, hRS, ← LinearMap.range_comp]
      change LinearMap.range ((T ^ L) * (T ^ j)) = _
      rw [← pow_add, Nat.add_comm]
    let qM : Module.End ℚ M := (Q.domRestrict M).codRestrict M hM
    let tN : Module.End ℚ N := (T.domRestrict N).codRestrict N hN
    let r : M →ₗ[ℚ] N := (R.domRestrict M).codRestrict N (by
      intro x
      rw [← hRM]
      exact ⟨x.val, x.property, rfl⟩)
    have hr : Function.Surjective r := by
      intro x
      have hx : x.val ∈ M.map R := hRM.symm ▸ x.property
      obtain ⟨y, hy, hxy⟩ := hx
      exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
    have hc : r.comp qM = tN.comp r := by
      ext x
      exact (congrArg (fun f : W →ₗ[ℚ] V => f x.val) hTR).symm
    have hquot : LinearMap.range qM ≤
        (LinearMap.range tN).comap r := by
      rintro _ ⟨x, rfl⟩
      exact ⟨r x, congrArg (fun f : M →ₗ[ℚ] N => f x) hc.symm⟩
    let qr := (LinearMap.range qM).mapQ (LinearMap.range tN) r hquot
    have hqr : Function.Surjective qr := by
      intro x
      obtain ⟨y, rfl⟩ := (LinearMap.range tN).mkQ_surjective x
      obtain ⟨z, rfl⟩ := hr y
      exact ⟨(LinearMap.range qM).mkQ z, rfl⟩
    have hdim := LinearMap.finrank_le_finrank_of_surjective hqr
    have quotient_ker {E : Type u} [AddCommGroup E] [Module ℚ E]
        [FiniteDimensional ℚ E] (f : Module.End ℚ E) :
        Module.finrank ℚ (E ⧸ LinearMap.range f) =
          Module.finrank ℚ (LinearMap.ker f) := by
      have ha := (LinearMap.range f).finrank_quotient_add_finrank
      have hb := f.finrank_range_add_finrank_ker
      omega
    rw [quotient_ker qM, quotient_ker tN] at hdim
    let emb : LinearMap.ker qM →ₗ[ℚ] LinearMap.ker (Q.domRestrict J) :=
      { toFun := fun x => ⟨⟨x.val.val, hMJ x.val.property⟩, by
          have hx := congrArg Subtype.val x.property
          exact hx⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hemb : Function.Injective emb := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z => z.val.val) h
    have hk := LinearMap.finrank_le_finrank_of_injective hemb
    have rank_ker {E : Type u} [AddCommGroup E] [Module ℚ E]
        [FiniteDimensional ℚ E] (f : Module.End ℚ E) (k : ℕ) :
        Module.finrank ℚ (LinearMap.ker (f.domRestrict (LinearMap.range (f ^ k)))) =
          Module.finrank ℚ (LinearMap.range (f ^ k)) -
            Module.finrank ℚ (LinearMap.range (f ^ (k + 1))) := by
      have hh := (f.domRestrict (LinearMap.range (f ^ k))).finrank_range_add_finrank_ker
      have hrange : LinearMap.range (f.domRestrict (LinearMap.range (f ^ k))) =
          LinearMap.range (f ^ (k + 1)) := by
        rw [LinearMap.range_domRestrict, ← LinearMap.range_comp]
        congr 1
        rw [pow_succ', Module.End.mul_eq_comp]
      rw [hrange] at hh
      omega
    have htker : LinearMap.ker tN = LinearMap.ker (T.domRestrict N) :=
      LinearMap.ker_codRestrict _ _ _
    rw [htker, rank_ker T (j + L)] at hdim
    rw [rank_ker Q j] at hk
    exact hdim.trans hk
  have adjacent (H : Type u) [Group H] [Fintype H] [Nontrivial H]
      {n : ℕ} (p r : Partition n) (hstep : dInf p r ≤ 1) :
      ∃ U V : Mat (MonoidAlgebra ℕ H) n n,
        (∀ i j g, 0 < (U i j).coeff g) ∧ (∀ i j g, 0 < (V i j).coeff g) ∧
        U * V = partitionMatrix H p ∧ V * U = partitionMatrix H r := by
    have blocks (a b : ℕ) (ha : a ≤ b + 1) (hb : b ≤ a + 1) :
        ∃ (P : Mat ℕ a b) (Q : Mat ℕ b a),
          (∀ i j, P i j ≤ 1) ∧ (∀ i j, Q i j ≤ 1) ∧
          P * Q = jordanShift a ∧ Q * P = jordanShift b := by
      classical
      have down (a b : ℕ) (hab : b ≤ a) (hba : a ≤ b + 1) :
          ∃ (P : Mat ℕ a b) (Q : Mat ℕ b a),
            (∀ i j, P i j ≤ 1) ∧ (∀ i j, Q i j ≤ 1) ∧
            P * Q = jordanShift a ∧ Q * P = jordanShift b := by
        let P : Mat ℕ a b := fun i j => if i.val = j.val then 1 else 0
        let Q : Mat ℕ b a := fun i j => if i.val + 1 = j.val then 1 else 0
        refine ⟨P, Q, ?_, ?_, ?_, ?_⟩
        · intro i j; dsimp [P]; split_ifs <;> omega
        · intro i j; dsimp [Q]; split_ifs <;> omega
        · ext i j
          change (∑ k : Fin b, (if i.val = k.val then 1 else 0) *
            (if k.val + 1 = j.val then 1 else 0)) = if i.val + 1 = j.val then 1 else 0
          by_cases hij : i.val + 1 = j.val
          · let k : Fin b := ⟨i.val, by have := j.isLt; omega⟩
            rw [Fintype.sum_eq_single k]
            · simp [k, hij]
            · intro t ht
              have ht' : i.val ≠ t.val := by
                intro h; apply ht; exact Fin.ext h.symm
              simp [ht']
          · rw [if_neg hij]
            apply Finset.sum_eq_zero
            intro k _
            split_ifs <;> simp_all
        · ext i j
          change (∑ k : Fin a, (if i.val + 1 = k.val then 1 else 0) *
            (if k.val = j.val then 1 else 0)) = if i.val + 1 = j.val then 1 else 0
          by_cases hij : i.val + 1 = j.val
          · let k : Fin a := ⟨j.val, by have := j.isLt; omega⟩
            rw [Fintype.sum_eq_single k]
            · simp [k, hij]
            · intro t ht
              have ht' : t.val ≠ j.val := by
                intro h; apply ht; exact Fin.ext h
              simp [ht']
          · rw [if_neg hij]
            apply Finset.sum_eq_zero
            intro k _
            split_ifs <;> simp_all
      by_cases hab : b ≤ a
      · exact down a b hab ha
      · obtain ⟨P, Q, hP, hQ, hPQ, hQP⟩ := down b a (by omega) hb
        exact ⟨Q, P, hQ, hP, hQP, hPQ⟩
    have product (H : Type u) [Group H] [Fintype H] (n : ℕ) :
        let q := Fintype.card H
        let z : MonoidAlgebra ℤ H := q • 1 - uniform H
        ∀ P Q : Mat ℕ n n,
          Matrix.of (fun i j => q • uniform H + P i j • z) *
            Matrix.of (fun i j => q • uniform H + Q i j • z) =
          fun i j => (q ^ 3 * n) • uniform H + (q * (P * Q) i j) • z := by
      classical
      dsimp only
      let q := Fintype.card H
      let u : MonoidAlgebra ℤ H := uniform H
      let z : MonoidAlgebra ℤ H := q • 1 - u
      have hub (g : H) : u * basis g = u := by
        calc
          u * basis g = ∑ h : H, basis (h * g) := by
            simp [u, uniform, basis, Finset.sum_mul]
          _ = u := by
            simpa [u, uniform, Function.comp_def] using
              (Finset.sum_comp_equiv (s := (Finset.univ : Finset H))
                (f := basis) (Equiv.mulRight g))
      have huu : u * u = q • u := by
        change u * (∑ g : H, basis g) = q • u
        rw [Finset.mul_sum]
        simp [hub, q]
      have huz : u * z = 0 := by
        dsimp only [z]
        rw [mul_sub, mul_smul_comm, mul_one, huu, sub_self]
      have hzu : z * u = 0 := by
        dsimp only [z]
        rw [sub_mul, smul_mul_assoc, one_mul, huu, sub_self]
      have hzz : z * z = q • z := by
        simp only [z, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, huu]
        simp only [nsmul_sub, smul_smul]
        abel
      intro P Q
      apply Matrix.ext
      intro i j
      simp only [Matrix.mul_apply, Matrix.of_apply]
      change (∑ k : Fin n, (q • u + P i k • z) * (q • u + Q k j • z)) =
        (q ^ 3 * n) • u + (q * ∑ k : Fin n, P i k * Q k j) • z
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, huu, huz, hzu, hzz,
        smul_zero, zero_add, add_zero, smul_smul]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_smul]
      have hc : n * (q * (q * q)) = q ^ 3 * n := by ring
      rw [hc]
      congr 1
      rw [← Finset.sum_smul]
      congr 1
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    classical
    let q := Fintype.card H
    let z : MonoidAlgebra ℤ H := q • 1 - uniform H
    have hq : 2 ≤ q := Fintype.one_lt_card
    have hqi : (2 : ℤ) ≤ q := by exact_mod_cast hq
    have bounds (i : Fin n) : coord p i ≤ coord r i + 1 ∧ coord r i ≤ coord p i + 1 := by
      have h := Finset.le_sup (s := (Finset.univ : Finset (Fin n)))
        (f := fun j => max (coord p j - coord r j) (coord r j - coord p j))
        (Finset.mem_univ i)
      change max (coord p i - coord r i) (coord r i - coord p i) ≤ dInf p r at h
      have := h.trans hstep
      omega
    choose P Q hP hQ hPQ hQP using
      fun i : Fin n => blocks (coord p i) (coord r i) (bounds i).1 (bounds i).2
    let PP : Mat ℕ n n := Matrix.reindex (blockCoordinates p) (blockCoordinates r)
      (Matrix.blockDiagonal' P)
    let QQ : Mat ℕ n n := Matrix.reindex (blockCoordinates r) (blockCoordinates p)
      (Matrix.blockDiagonal' Q)
    have bd_bound {a b : Fin n → ℕ} (M : ∀ i, Mat ℕ (a i) (b i))
        (hM : ∀ i j k, M i j k ≤ 1) : ∀ j k, Matrix.blockDiagonal' M j k ≤ 1 := by
      rintro ⟨i, j⟩ ⟨t, k⟩
      by_cases h : i = t
      · subst t
        simpa using hM i j k
      · simp [Matrix.blockDiagonal'_apply, h]
    have hPP (i j) : PP i j ≤ 1 := bd_bound P hP _ _
    have hQQ (i j) : QQ i j ≤ 1 := bd_bound Q hQ _ _
    have hPPQQ : PP * QQ = partitionShift p := by
      dsimp only [PP, QQ, partitionShift, Matrix.reindex_apply]
      rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]
      have hh : (fun i => P i * Q i) = (fun i => jordanShift (coord p i)) := funext hPQ
      rw [hh]
    have hQQPP : QQ * PP = partitionShift r := by
      dsimp only [PP, QQ, partitionShift, Matrix.reindex_apply]
      rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]
      have hh : (fun i => Q i * P i) = (fun i => jordanShift (coord r i)) := funext hQP
      rw [hh]
    have huc (g : H) : (uniform H).coeff g = 1 := by
      simp [uniform, basis, MonoidAlgebra.coeff_sum]
    have positive (b : ℕ) (hb : b ≤ 1) (g : H) :
        0 < (q • uniform H + b • z).coeff g := by
      have hcoeff : (q • uniform H + b • z).coeff g =
          (q : ℤ) + (b : ℤ) * ((q : ℤ) * (if (1 : H) = g then 1 else 0) - 1) := by
        simp only [z, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_sub,
          MonoidAlgebra.coeff_smul, Finsupp.add_apply, Finsupp.sub_apply,
          Finsupp.smul_apply, huc, MonoidAlgebra.one_def,
          MonoidAlgebra.coeff_single, Finsupp.single_apply]
        simp only [nsmul_eq_mul, mul_one]
      rw [hcoeff]
      have hb' : b = 0 ∨ b = 1 := by omega
      rcases hb' with rfl | rfl
      · simp only [Nat.cast_zero, zero_mul, add_zero]; omega
      · simp only [Nat.cast_one, one_mul]
        split_ifs <;> nlinarith
    let UZ : Mat (MonoidAlgebra ℤ H) n n := Matrix.of fun i j => q • uniform H + PP i j • z
    let VZ : Mat (MonoidAlgebra ℤ H) n n := Matrix.of fun i j => q • uniform H + QQ i j • z
    let U : Mat (MonoidAlgebra ℕ H) n n := fun i j => toNat (UZ i j)
    let V : Mat (MonoidAlgebra ℕ H) n n := fun i j => toNat (VZ i j)
    have lift_toNat (x : MonoidAlgebra ℤ H) (hx : ∀ g, 0 ≤ x.coeff g) :
        liftNat H (toNat x) = x := by
      ext g
      simp [liftNat, toNat, Int.toNat_of_nonneg (hx g)]
    have toNat_lift (x : MonoidAlgebra ℕ H) : toNat (liftNat H x) = x := by
      ext g
      simp [liftNat, toNat]
    have hUZ : U.map (liftNat H) = UZ := by
      apply Matrix.ext
      intro i j
      exact lift_toNat _ (fun g => (positive _ (hPP i j) g).le)
    have hVZ : V.map (liftNat H) = VZ := by
      apply Matrix.ext
      intro i j
      exact lift_toNat _ (fun g => (positive _ (hQQ i j) g).le)
    have mulmap (X Y : Mat (MonoidAlgebra ℕ H) n n) :
        (X * Y).map (liftNat H) = X.map (liftNat H) * Y.map (liftNat H) := by
      apply Matrix.ext
      intro i j
      simp [Matrix.mul_apply, map_sum, map_mul]
    have hUV : U * V = partitionMatrix H p := by
      have hz : (U * V).map (liftNat H) =
          fun i j => (q ^ 3 * n) • uniform H + (q * partitionShift p i j) • z := by
        rw [mulmap, hUZ, hVZ]
        simpa only [UZ, VZ, q, z, hPPQQ] using product H n PP QQ
      have := congrArg (fun X : Mat (MonoidAlgebra ℤ H) n n =>
        fun i j => toNat (X i j)) hz
      apply Matrix.ext
      intro i j
      have hij := congrFun (congrFun this i) j
      simpa only [Matrix.map_apply, toNat_lift, partitionMatrix, q, z] using hij
    have hVU : V * U = partitionMatrix H r := by
      have hz : (V * U).map (liftNat H) =
          fun i j => (q ^ 3 * n) • uniform H + (q * partitionShift r i j) • z := by
        rw [mulmap, hUZ, hVZ]
        simpa only [UZ, VZ, q, z, hQQPP] using product H n QQ PP
      have := congrArg (fun X : Mat (MonoidAlgebra ℤ H) n n =>
        fun i j => toNat (X i j)) hz
      apply Matrix.ext
      intro i j
      have hij := congrFun (congrFun this i) j
      simpa only [Matrix.map_apply, toNat_lift, partitionMatrix, q, z] using hij
    refine ⟨U, V, ?_, ?_, hUV, hVU⟩
    · intro i j g
      change 0 < ((UZ i j).coeff g).toNat
      exact Int.pos_iff_toNat_pos.mp (positive _ (hPP i j) g)
    · intro i j g
      change 0 < ((VZ i j).coeff g).toNat
      exact Int.pos_iff_toNat_pos.mp (positive _ (hQQ i j) g)
  have endpoint_action (H : Type u) [Group H] [Fintype H] [Nontrivial H]
      {n : ℕ} (hn : 1 ≤ n) :
      let I : Ideal (MonoidAlgebra ℚ H) := RingHom.ker rationalAugmentation.toRingHom
      ∃ act : ∀ {r s : ℕ}, Mat (MonoidAlgebra ℚ H) r s →
          (Fin s → I) →ₗ[ℚ] (Fin r → I),
        (∀ {r s t : ℕ} (A : Mat (MonoidAlgebra ℚ H) r s)
          (B : Mat (MonoidAlgebra ℚ H) s t), act (A * B) = (act A).comp (act B)) ∧
        (∀ r, act (1 : Mat (MonoidAlgebra ℚ H) r r) = 1) ∧
        ∀ (p : Partition n) k,
          Module.finrank ℚ
            (LinearMap.range ((act ((partitionMatrix H p).map naturalToRational)) ^ k)) =
            (Fintype.card H - 1) * (∑ i, (coord p i - k)) := by
    have shift_rank {n : ℕ} (p : Partition n) (K : Type u) [AddCommGroup K] [Module ℚ K]
        [FiniteDimensional ℚ K] (c : ℚ) (hc : c ≠ 0) :
        let E := (Σ i : Fin n, Fin (coord p i)) → K
        ∃ F : Module.End ℚ E,
          (∀ x i t, F x ⟨i, t⟩ =
            if h : t.val + 1 < coord p i then c • x ⟨i, ⟨t.val + 1, h⟩⟩ else 0) ∧
          ∀ k, Module.finrank ℚ (LinearMap.range (F ^ k)) =
            (∑ i, (coord p i - k)) * Module.finrank ℚ K := by
      classical
      dsimp only
      let E := (Σ i : Fin n, Fin (coord p i)) → K
      let f (k : ℕ) : Module.End ℚ E :=
        { toFun := fun x a => if h : a.2.val + k < coord p a.1 then
            x ⟨a.1, ⟨a.2.val + k, h⟩⟩ else 0
          map_add' := by
            intro x y
            funext a
            change (if h : a.2.val + k < coord p a.1 then
              x ⟨a.1, ⟨a.2.val + k, h⟩⟩ + y ⟨a.1, ⟨a.2.val + k, h⟩⟩ else 0) =
              (if h : a.2.val + k < coord p a.1 then x ⟨a.1, ⟨a.2.val + k, h⟩⟩ else 0) +
              (if h : a.2.val + k < coord p a.1 then y ⟨a.1, ⟨a.2.val + k, h⟩⟩ else 0)
            split_ifs <;> simp
          map_smul' := by
            intro r x
            funext a
            change (if h : a.2.val + k < coord p a.1 then
              r • x ⟨a.1, ⟨a.2.val + k, h⟩⟩ else 0) =
              r • (if h : a.2.val + k < coord p a.1 then x ⟨a.1, ⟨a.2.val + k, h⟩⟩ else 0)
            split_ifs <;> simp }
      have hf (k : ℕ) : f k = (f 1) ^ k := by
        induction k with
        | zero =>
            apply LinearMap.ext
            intro x
            funext a
            rcases a with ⟨i, t⟩
            simp [f]
        | succ k ih =>
            rw [pow_succ', ← ih]
            apply LinearMap.ext
            intro x
            funext a
            rcases a with ⟨i, t⟩
            change (if h : t.val + (k + 1) < coord p i then
              x ⟨i, ⟨t.val + (k + 1), h⟩⟩ else 0) =
              f 1 (f k x) ⟨i, t⟩
            change (if h : t.val + (k + 1) < coord p i then
              x ⟨i, ⟨t.val + (k + 1), h⟩⟩ else 0) =
              if h : t.val + 1 < coord p i then
                (if h' : t.val + 1 + k < coord p i then
                  x ⟨i, ⟨t.val + 1 + k, h'⟩⟩ else 0) else 0
            have hsum : t.val + (k + 1) = t.val + 1 + k := by omega
            rw [hsum]
            by_cases h : t.val + 1 < coord p i
            · rw [dif_pos h]
            · have hk : ¬ t.val + 1 + k < coord p i := by omega
              rw [dif_neg h, dif_neg hk]
      refine ⟨c • f 1, ?_, ?_⟩
      · intro x i t
        change c • (if h : t.val + 1 < coord p i then
          x ⟨i, ⟨t.val + 1, h⟩⟩ else 0) = _
        split_ifs <;> simp only [smul_zero]
      · intro k
        rw [smul_pow, ← hf k, LinearMap.range_smul _ _ (pow_ne_zero _ hc)]
        let B := (Σ i : Fin n, Fin (coord p i - k)) → K
        let inc : B →ₗ[ℚ] E :=
          { toFun := fun x a => if h : a.2.val < coord p a.1 - k then
              x ⟨a.1, ⟨a.2.val, h⟩⟩ else 0
            map_add' := by
              intro x y
              funext a
              change (if h : a.2.val < coord p a.1 - k then
                x ⟨a.1, ⟨a.2.val, h⟩⟩ + y ⟨a.1, ⟨a.2.val, h⟩⟩ else 0) =
                (if h : a.2.val < coord p a.1 - k then x ⟨a.1, ⟨a.2.val, h⟩⟩ else 0) +
                (if h : a.2.val < coord p a.1 - k then y ⟨a.1, ⟨a.2.val, h⟩⟩ else 0)
              split_ifs <;> simp
            map_smul' := by
              intro r x
              funext a
              change (if h : a.2.val < coord p a.1 - k then r • x ⟨a.1, ⟨a.2.val, h⟩⟩ else 0) =
                r • (if h : a.2.val < coord p a.1 - k then x ⟨a.1, ⟨a.2.val, h⟩⟩ else 0)
              split_ifs <;> simp }
        let tail : E →ₗ[ℚ] B :=
          { toFun := fun x a => x ⟨a.1, ⟨a.2.val + k, by have := a.2.isLt; omega⟩⟩
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        have hcomp : f k = inc.comp tail := by
          apply LinearMap.ext
          intro x
          funext a
          rcases a with ⟨i, t⟩
          change (if h : t.val + k < coord p i then
            x ⟨i, ⟨t.val + k, h⟩⟩ else 0) =
            if h : t.val < coord p i - k then
              x ⟨i, ⟨t.val + k, by omega⟩⟩ else 0
          by_cases h : t.val + k < coord p i
          · simp only [dif_pos h, dif_pos (show t.val < coord p i - k by omega)]
          · simp only [dif_neg h, dif_neg (show ¬ t.val < coord p i - k by omega)]
        have hinc : Function.Injective inc := by
          intro x y h
          funext ⟨i, t⟩
          have he := congrArg (fun z : E => z ⟨i, ⟨t.val, by have := t.isLt; omega⟩⟩) h
          simpa [inc, t.isLt] using he
        have htail : Function.Surjective tail := by
          intro x
          let y : E := fun a => if h : k ≤ a.2.val ∧ a.2.val - k < coord p a.1 - k then
            x ⟨a.1, ⟨a.2.val - k, h.2⟩⟩ else 0
          refine ⟨y, ?_⟩
          funext ⟨i, t⟩
          change (if h : k ≤ t.val + k ∧ t.val + k - k < coord p i - k then
            x ⟨i, ⟨t.val + k - k, h.2⟩⟩ else 0) = x ⟨i, t⟩
          rw [dif_pos ⟨by omega, by have := t.isLt; omega⟩]
          simp only [Nat.add_sub_cancel]
        rw [hcomp, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr htail),
          LinearMap.finrank_range_of_inj hinc]
        change Module.finrank ℚ B = _
        simp only [B, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, Fintype.card_sigma, Fintype.card_fin, Nat.cast_id]
    classical
    let q := Fintype.card H
    let I : Ideal (MonoidAlgebra ℚ H) := RingHom.ker rationalAugmentation.toRingHom
    let act {r s : ℕ} (A : Mat (MonoidAlgebra ℚ H) r s) :
        (Fin s → I) →ₗ[ℚ] (Fin r → I) :=
      { toFun := fun x i => ∑ j, A i j • x j
        map_add' := by intro x y; funext i; simp [smul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro c x
          funext i
          simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]
          apply Finset.sum_congr rfl
          intro j _
          exact smul_comm (A i j) c (x j) }
    have mulact {r s t : ℕ} (A : Mat (MonoidAlgebra ℚ H) r s)
        (B : Mat (MonoidAlgebra ℚ H) s t) : act (A * B) = (act A).comp (act B) := by
      apply LinearMap.ext
      intro x
      funext i
      change (∑ j, (A * B) i j • x j) = ∑ j, A i j • (∑ k, B j k • x k)
      simp_rw [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
      rw [Finset.sum_comm]
    have oneact (r : ℕ) : act (1 : Mat (MonoidAlgebra ℚ H) r r) = 1 := by
      apply LinearMap.ext
      intro x
      funext i
      change (∑ j, (1 : Mat (MonoidAlgebra ℚ H) r r) i j • x j) = x i
      simp [Matrix.one_apply]
    let castZ : MonoidAlgebra ℤ H →+* MonoidAlgebra ℚ H :=
      MonoidAlgebra.mapRingHom H (Int.castRingHom ℚ)
    let uQ := castZ (uniform H)
    have hucZ (g : H) : (uniform H).coeff g = 1 := by
      simp [uniform, basis, MonoidAlgebra.coeff_sum]
    have hucQ (g : H) : uQ.coeff g = 1 := by
      simp [uQ, castZ, MonoidAlgebra.coeff_mapRingHom, hucZ]
    have hu (x : I) : uQ • x = 0 := by
      apply Subtype.ext
      change uQ * x.val = 0
      ext g
      rw [MonoidAlgebra.coeff_mul_apply_right]
      rw [Finsupp.sum_fintype _ _ (fun _ => mul_zero _)]
      simp only [hucQ, one_mul]
      rw [← rationalAugmentation_eq_sum]
      exact x.property
    have shift_bound (p : Partition n) (i j) : partitionShift p i j ≤ 1 := by
      have hb (x y : Σ k : Fin n, Fin (coord p k)) :
          Matrix.blockDiagonal' (fun k => jordanShift (coord p k)) x y ≤ 1 := by
        rcases x with ⟨k, a⟩
        rcases y with ⟨t, b⟩
        by_cases h : k = t
        · subst t
          simp only [Matrix.blockDiagonal'_apply]
          dsimp [jordanShift]
          split_ifs <;> omega
        · simp [Matrix.blockDiagonal'_apply, h]
      exact hb _ _
    have hq : 2 ≤ q := Fintype.one_lt_card
    have hqi : (2 : ℤ) ≤ q := by exact_mod_cast hq
    have hni : (1 : ℤ) ≤ n := by exact_mod_cast hn
    have base_pos : (q : ℤ) ^ 3 * n - q > 0 := by
      have h2 : (q : ℤ) ^ 2 ≥ 4 := by nlinarith
      have h3 : (q : ℤ) ^ 3 ≥ 2 * q := by nlinarith
      nlinarith
    have endpoint_positive (p : Partition n) (i j) (g : H) :
        0 < ((q ^ 3 * n) • uniform H + (q * partitionShift p i j) •
          (q • (1 : MonoidAlgebra ℤ H) - uniform H)).coeff g := by
      have hb := shift_bound p i j
      have hb' : partitionShift p i j = 0 ∨ partitionShift p i j = 1 := by omega
      have hcoeff : ((q ^ 3 * n) • uniform H + (q * partitionShift p i j) •
          (q • (1 : MonoidAlgebra ℤ H) - uniform H)).coeff g =
          (q : ℤ) ^ 3 * n + ((q : ℤ) * partitionShift p i j) *
            ((q : ℤ) * (if (1 : H) = g then 1 else 0) - 1) := by
        simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_sub,
          MonoidAlgebra.coeff_smul, Finsupp.add_apply, Finsupp.sub_apply,
          Finsupp.smul_apply, hucZ, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single,
          Finsupp.single_apply]
        simp only [nsmul_eq_mul, mul_one, Nat.cast_mul, Nat.cast_pow]
      rw [hcoeff]
      rcases hb' with hb | hb
      · rw [hb]; simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]; positivity
      · rw [hb]; simp only [Nat.cast_one, mul_one]
        split_ifs <;> nlinarith
    have cast_toNat (x : MonoidAlgebra ℤ H) (hx : ∀ g, 0 ≤ x.coeff g) :
        naturalToRational (toNat x) = castZ x := by
      ext g
      have hg : (((x.coeff g).toNat : ℕ) : ℤ) = x.coeff g := Int.toNat_of_nonneg (hx g)
      change ((x.coeff g).toNat : ℚ) = (x.coeff g : ℚ)
      exact_mod_cast hg
    have entry (p : Partition n) (i j) (x : I) :
        naturalToRational (partitionMatrix H p i j) • x =
          ((q : ℚ) ^ 2 * (partitionShift p i j : ℚ)) • x := by
      unfold partitionMatrix
      rw [cast_toNat _ (fun g => (endpoint_positive p i j g).le)]
      simp only [map_add, map_nsmul, map_sub, map_one]
      change ((q ^ 3 * n) • uQ + (q * partitionShift p i j) •
        (q • (1 : MonoidAlgebra ℚ H) - uQ)) • x = _
      simp only [add_smul, smul_assoc, hu, smul_zero, zero_add, sub_smul,
        one_smul, sub_zero, smul_smul]
      rw [← Nat.cast_smul_eq_nsmul ℚ]
      congr 1
      push_cast
      ring
    refine ⟨fun {_ _} => act, @mulact, oneact, ?_⟩
    intro p k
    have hdim : Module.finrank ℚ I = q - 1 := by
      have hne : (rationalAugmentation (H := H)).toLinearMap ≠ 0 := by
        intro h
        have hh := congrArg (fun f : MonoidAlgebra ℚ H →ₗ[ℚ] ℚ =>
          f (MonoidAlgebra.single 1 1)) h
        simp at hh
      have h := Module.Dual.finrank_ker_add_one_of_ne_zero hne
      have hd : Module.finrank ℚ (MonoidAlgebra ℚ H) = q := by
        rw [(MonoidAlgebra.coeffLinearEquiv ℚ).finrank_eq]
        exact Module.finrank_finsupp_self ℚ
      change Module.finrank ℚ (LinearMap.ker rationalAugmentation.toLinearMap) = _
      omega
    obtain ⟨F, hF, hrank⟩ := shift_rank p I ((q : ℚ) ^ 2) (pow_ne_zero _ (by
      exact_mod_cast (show q ≠ 0 by omega)))
    let e : (Fin n → I) ≃ₗ[ℚ] ((Σ i : Fin n, Fin (coord p i)) → I) :=
      { toFun := fun x a => x (blockCoordinates p a)
        invFun := fun x a => x ((blockCoordinates p).symm a)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := by intro x; funext a; simp
        right_inv := by intro x; funext a; simp }
    let T := act ((partitionMatrix H p).map naturalToRational)
    have hc : e.conjRingEquiv T = F := by
      apply LinearMap.ext
      intro x
      funext a
      rcases a with ⟨i, t⟩
      rw [hF]
      change (∑ j : Fin n, naturalToRational
        (partitionMatrix H p (blockCoordinates p ⟨i, t⟩) j) •
        x ((blockCoordinates p).symm j)) = _
      simp_rw [entry]
      rw [← (blockCoordinates p).sum_comp]
      simp only [Equiv.symm_apply_apply, partitionShift, Matrix.reindex_apply,
        Matrix.submatrix_apply, Equiv.symm_apply_apply]
      rw [Fintype.sum_sigma, Fintype.sum_eq_single i]
      · simp only [Matrix.blockDiagonal'_apply]
        by_cases h : t.val + 1 < coord p i
        · let s : Fin (coord p i) := ⟨t.val + 1, h⟩
          rw [Fintype.sum_eq_single s]
          · simp [jordanShift, s, h]
          · intro v hv
            have hv' : t.val + 1 ≠ v.val := by
              intro he
              apply hv
              exact Fin.ext he.symm
            simp [jordanShift, hv']
        · rw [dif_neg h]
          apply Finset.sum_eq_zero
          intro v _
          have hv' : t.val + 1 ≠ v.val := by have := v.isLt; omega
          simp [jordanShift, hv']
      · intro j hj
        apply Finset.sum_eq_zero
        intro v _
        simp [Matrix.blockDiagonal'_apply, Ne.symm hj]
    have heq : LinearMap.range ((e.conjRingEquiv T) ^ k) =
        (LinearMap.range (T ^ k)).map e.toLinearMap := by
      rw [← map_pow]
      change LinearMap.range ((e.toLinearMap.comp (T ^ k)).comp e.symm.toLinearMap) = _
      rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr e.symm.surjective),
        LinearMap.range_comp]
    have hdimmap := e.finrank_map_eq (LinearMap.range (T ^ k))
    have hr := hrank k
    rw [← hc, heq, hdimmap, hdim] at hr
    exact hr.trans (Nat.mul_comm _ _)
  have attained (H : Type u) [Group H] [Fintype H] {n : ℕ}
      (adj : ∀ p r : Partition n, dInf p r ≤ 1 →
        ∃ U V : Mat (MonoidAlgebra ℕ H) n n,
          U * V = partitionMatrix H p ∧ V * U = partitionMatrix H r)
      (p r : Partition n) :
      ExchangeChain (MonoidAlgebra ℕ H) (partitionMatrix H p) (partitionMatrix H r) (dInf p r) := by
    have fold (D : ℕ) (γ : Fin (D + 1) → Partition n)
        (h : ∀ k : Fin D, dInf (γ ⟨k.val, by omega⟩) (γ ⟨k.val + 1, by omega⟩) ≤ 1) :
        ExchangeChain (MonoidAlgebra ℕ H) (partitionMatrix H (γ 0))
          (partitionMatrix H (γ ⟨D, by omega⟩)) D := by
      induction D with
      | zero => exact ExchangeChain.nil _
      | succ D ih =>
        obtain ⟨U, V, hUV, hVU⟩ := adj (γ 0) (γ 1) (h 0)
        have ht := ih (fun k => γ k.succ) (fun k => h k.succ)
        change ExchangeChain (MonoidAlgebra ℕ H) (partitionMatrix H (γ 1))
          (partitionMatrix H (γ ⟨D + 1, by omega⟩)) D at ht
        rw [← hVU] at ht
        rw [← hUV]
        exact ExchangeChain.cons U V ht
    obtain ⟨γ, hγ⟩ := (partition_lInf_geodesic p r).1
    simpa only [hγ.1, hγ.2.1] using fold (dInf p r) γ hγ.2.2.1
  have cumulative {R : Type u} [Semiring R] {n m L : ℕ}
      {A : Mat R n n} {B : Mat R m m} (c : ExchangeChain R A B L) :
      ∃ (X : Mat R n m) (Y : Mat R m n),
        A * X = X * B ∧ B * Y = Y * A ∧ X * Y = A ^ L ∧ Y * X = B ^ L := by
    induction c with
    | nil A => exact ⟨1, 1, by simp, by simp, by simp, by simp⟩
    | @cons n k m L U V B tail ih =>
      obtain ⟨X, Y, hX, hY, hXY, hYX⟩ := ih
      refine ⟨U * X, Y * V, ?_, ?_, ?_, ?_⟩
      · calc
          (U * V) * (U * X) = U * ((V * U) * X) := by simp only [Matrix.mul_assoc]
          _ = (U * X) * B := by rw [hX]; simp only [Matrix.mul_assoc]
      · calc
          B * (Y * V) = (B * Y) * V := by simp only [Matrix.mul_assoc]
          _ = (Y * V) * (U * V) := by rw [hY]; simp only [Matrix.mul_assoc]
      · calc
          (U * X) * (Y * V) = U * (X * Y) * V := by simp only [Matrix.mul_assoc]
          _ = (U * V) ^ (L + 1) := by rw [hXY, rectangular_exchange_power]
      · calc
          (Y * V) * (U * X) = Y * ((V * U) * X) := by simp only [Matrix.mul_assoc]
          _ = (Y * X) * B := by rw [hX]; simp only [Matrix.mul_assoc]
          _ = B ^ (L + 1) := by rw [hYX, pow_succ]
  have coordinate_bound {n : ℕ} (p r : Partition n) (L q : ℕ) (hq : 0 < q)
      (hpr : ∀ j,
        q * (∑ i, (coord p i - (j + L))) - q * (∑ i, (coord p i - (j + L + 1))) ≤
        q * (∑ i, (coord r i - j)) - q * (∑ i, (coord r i - (j + 1))))
      (hrp : ∀ j,
        q * (∑ i, (coord r i - (j + L))) - q * (∑ i, (coord r i - (j + L + 1))) ≤
        q * (∑ i, (coord p i - j)) - q * (∑ i, (coord p i - (j + 1)))) : dInf p r ≤ L := by
    classical
    have layer (p : Partition n) (j : ℕ) :
        q * (∑ i, (coord p i - j)) - q * (∑ i, (coord p i - (j + 1))) =
        q * (Finset.univ.filter (fun i => j < coord p i)).card := by
      rw [← Nat.mul_sub_left_distrib, ← Finset.sum_tsub_distrib _ (by intro i _; omega)]
      congr 1
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> omega
    have ant (p : Partition n) {i j : Fin n} (hij : i ≤ j) : coord p j ≤ coord p i := by
      exact p.property.2.1.rel_get_of_le (by simpa using hij)
    have bound (p r : Partition n)
        (h : ∀ j, (Finset.univ.filter (fun i => j + L < coord p i)).card ≤
          (Finset.univ.filter (fun i => j < coord r i)).card) (i : Fin n) :
        coord p i ≤ coord r i + L := by
      by_contra hi
      let j := coord r i
      have hl : Finset.Iic i ⊆ Finset.univ.filter (fun k => j + L < coord p k) := by
        intro k hk
        have ha := ant p (Finset.mem_Iic.mp hk)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        dsimp [j]
        omega
      have hr : Finset.univ.filter (fun k => j < coord r k) ⊆ Finset.Iio i := by
        intro k hk
        have hk' := (Finset.mem_filter.mp hk).2
        apply Finset.mem_Iio.mpr
        by_contra hki
        have ha := ant r (le_of_not_gt hki)
        dsimp [j] at hk'
        omega
      have h1 := Finset.card_le_card hl
      have h2 := (h j).trans (Finset.card_le_card hr)
      simp only [Fin.card_Iic, Fin.card_Iio] at h1 h2
      omega
    have hcpr (j : ℕ) := hpr j
    have hcrp (j : ℕ) := hrp j
    simp only [layer] at hcpr hcrp
    have hbpr := bound p r (fun j => (Nat.mul_le_mul_left_iff hq).mp (hcpr j))
    have hbrp := bound r p (fun j => (Nat.mul_le_mul_left_iff hq).mp (hcrp j))
    apply Finset.sup_le
    intro i _
    have h1 := hbpr i
    have h2 := hbrp i
    omega
  constructor
  · refine ⟨attained H ?_ p r⟩
    intro a b hab
    obtain ⟨U, V, _, _, hUV, hVU⟩ := adjacent H a b hab
    exact ⟨U, V, hUV, hVU⟩
  · intro L c
    obtain ⟨act, hmul, hone, hrank⟩ := endpoint_action H hn
    have powact {a : ℕ} (A : Mat (MonoidAlgebra ℚ H) a a) (k : ℕ) :
        act (A ^ k) = (act A) ^ k := by
      induction k with
      | zero => simpa only [pow_zero] using hone a
      | succ k ih => rw [pow_succ, hmul, ih, pow_succ, Module.End.mul_eq_comp]
    have cq := map_exchange_chain naturalToRational.toNonUnitalRingHom c
    obtain ⟨X, Y, hX, hY, hXY, hYX⟩ := cumulative cq
    let A := (partitionMatrix H p).map naturalToRational
    let B := (partitionMatrix H r).map naturalToRational
    have hTR : (act A).comp (act X) = (act X).comp (act B) := by
      rw [← hmul, ← hmul]
      exact congrArg (fun Z : Mat (MonoidAlgebra ℚ H) n n => act Z) hX
    have hQS : (act B).comp (act Y) = (act Y).comp (act A) := by
      rw [← hmul, ← hmul]
      exact congrArg (fun Z : Mat (MonoidAlgebra ℚ H) n n => act Z) hY
    have hRS : (act X).comp (act Y) = (act A) ^ L := by
      rw [← hmul, hXY, powact]
      rfl
    have hSR : (act Y).comp (act X) = (act B) ^ L := by
      rw [← hmul, hYX, powact]
      rfl
    have hpr := quotient_layer (act A) (act B) (act X) (act Y) L hTR hQS hRS
    have hrp := quotient_layer (act B) (act A) (act Y) (act X) L hQS hTR hSR
    dsimp only [A, B] at hpr hrp
    apply coordinate_bound p r L (Fintype.card H - 1) (by
      have hq : 2 ≤ Fintype.card H := Fintype.one_lt_card
      omega)
    · intro j
      simpa only [hrank] using hpr j
    · intro j
      simpa only [hrank] using hrp j

#print axioms theorem32_2

end
end D5.S3.ConceptDynamics.Coding.FixedPositivePartitionSseDistance
