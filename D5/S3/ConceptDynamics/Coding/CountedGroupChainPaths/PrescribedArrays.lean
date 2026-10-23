/- GID: D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The prescribed finite G34 array preserves labels and has unique rows. -/

import D5.S3.ConceptDynamics.Coding.CountedGroupChainPaths.FactorPaths

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Coding.CountedGroupChainPaths

open CountedGroupOverlap
open RectangularNilpotenceBarrier

universe u
variable {H : Type u} [Group H] [Fintype H]

private theorem orderedAt_label [LinearOrder H] {n k : ℕ}
    (U : GroupMat H n k) (V : GroupMat H k n) (i j : Fin n) (e : At (U * V) i j) :
    (orderedAtEquiv U V i j e).2.1.1 * (orderedAtEquiv U V i j e).2.2.1 = e.1 := by
  change (orderedFiberEquiv U V i j e.1 e.2).2.1 *
    ((orderedFiberEquiv U V i j e.1 e.2).2.1⁻¹ * e.1) = e.1
  simp

private theorem orderedAt_inv_label [LinearOrder H] {n k : ℕ}
    (U : GroupMat H n k) (V : GroupMat H k n) (i j : Fin n)
    (p : Σ v : Fin k, At U i v × At V v j) :
    ((orderedAtEquiv U V i j).symm p).1 = p.2.1.1 * p.2.2.1 := by
  exact (orderedAt_label U V i j ((orderedAtEquiv U V i j).symm p)).symm.trans
    (congrArg (fun q : Σ v : Fin k, At U i v × At V v j => q.2.1.1 * q.2.2.1)
      ((orderedAtEquiv U V i j).apply_symm_apply p))

omit [Fintype H] in
private theorem pathSnoc_label {n k m L : ℕ} (f : Factors H n k L)
    (M : GroupMat H k m) (i : Fin n) (j : Fin m)
    (p : FactorPath (factorSnoc f M) i j) :
    factorLabel (factorSnoc f M) p =
      factorLabel f (pathSnocEquiv f M i j p).2.1 *
        (pathSnocEquiv f M i j p).2.2.1 := by
  induction f generalizing m with
  | nil n =>
    rcases p with ⟨v, g, c, ⟨⟨w, hwv, hwj⟩⟩⟩
    subst w
    subst v
    change g * 1 = 1 * g
    simp
  | @cons n t k L N f ih =>
    change p.2.1 * factorLabel (factorSnoc f M) p.2.2.2 =
      (p.2.1 * factorLabel f (pathSnocEquiv f M p.1 j p.2.2.2).2.1) *
        (pathSnocEquiv f M p.1 j p.2.2.2).2.2.1
    rw [ih M p.1 j p.2.2.2, mul_assoc]

omit [Fintype H] in
private theorem pathSnoc_inv_label {n k m L : ℕ} (f : Factors H n k L)
    (M : GroupMat H k m) (i : Fin n) (j : Fin m)
    (p : Σ v : Fin k, FactorPath f i v × At M v j) :
    factorLabel (factorSnoc f M) ((pathSnocEquiv f M i j).symm p) =
      factorLabel f p.2.1 * p.2.2.1 := by
  exact (pathSnoc_label f M i j ((pathSnocEquiv f M i j).symm p)).trans
    (congrArg (fun q : Σ v : Fin k, FactorPath f i v × At M v j =>
      factorLabel f q.2.1 * q.2.2.1) ((pathSnocEquiv f M i j).apply_symm_apply p))

/-- A peeling row preserves the ordered product of every saved and internal label. -/
private theorem peelRow_label [LinearOrder H] {n k : ℕ}
    (U : GroupMat H n k) (V : GroupMat H k n) (l : ℕ) (i j : Fin n)
    (p : Word (U * V) (l + 1) i j) :
    factorLabel (wordFactors (U * V) (l + 1)) p =
      (peelRow U V l i j p).2.2.1.1 *
        factorLabel (wordFactors (V * U) l) (peelRow U V l i j p).2.2.2.1 *
          (peelRow U V l i j p).2.2.2.2.1 := by
  induction l generalizing i with
  | zero =>
    rcases p with ⟨v, g, c, ⟨⟨w, hwv, hwj⟩⟩⟩
    subst w
    subst v
    change g * 1 = (orderedAtEquiv U V i j ⟨g, c⟩).2.1.1 * 1 *
      (orderedAtEquiv U V i j ⟨g, c⟩).2.2.1
    simpa only [mul_one] using (orderedAt_label U V i j ⟨g, c⟩).symm
  | succ l ih =>
    let a : At (U * V) i p.1 := ⟨p.2.1, p.2.2.1⟩
    let d := orderedAtEquiv U V i p.1 a
    let t := peelRow U V l p.1 j p.2.2.2
    let b := (orderedAtEquiv V U d.1 t.1).symm ⟨p.1, d.2.2, t.2.2.1⟩
    change a.1 * factorLabel (wordFactors (U * V) (l + 1)) p.2.2.2 =
      d.2.1.1 * (b.1 * factorLabel (wordFactors (V * U) l) t.2.2.2.1) * t.2.2.2.2.1
    have hb : b.1 = d.2.2.1 * t.2.2.1.1 :=
      orderedAt_inv_label V U d.1 t.1 ⟨p.1, d.2.2, t.2.2.1⟩
    rw [hb, ih]
    have ha : a.1 = d.2.1.1 * d.2.2.1 := (orderedAt_label U V i p.1 a).symm
    simp only [ha, t, mul_assoc]

private theorem psi0_inv_label [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i j : Fin n) (w : Word A L i j) :
    factorLabel (forwardFactors c) ((psi0 c i j).symm w).2.1 *
      factorLabel (backwardFactors c) ((psi0 c i j).symm w).2.2 =
        factorLabel (wordFactors A L) w := by
  induction c with
  | nil A => simp only [forwardFactors, backwardFactors, wordFactors, factorLabel, mul_one]
  | @cons n k m L A B C U V hA hB c ih =>
    subst A
    subst B
    let t := peelRow U V L i j w
    let p := (psi0 c t.1 t.2.1).symm t.2.2.2.1
    change (t.2.2.1.1 * factorLabel (forwardFactors c) p.2.1) *
      factorLabel (factorSnoc (backwardFactors c) V)
        ((pathSnocEquiv (backwardFactors c) V p.1 j).symm
          ⟨t.2.1, p.2.2, t.2.2.2.2⟩) = factorLabel (wordFactors (U * V) (L + 1)) w
    rw [pathSnoc_inv_label]
    calc
      (t.2.2.1.1 * factorLabel (forwardFactors c) p.2.1) *
          (factorLabel (backwardFactors c) p.2.2 * t.2.2.2.2.1) =
          t.2.2.1.1 * (factorLabel (forwardFactors c) p.2.1 *
            factorLabel (backwardFactors c) p.2.2) * t.2.2.2.2.1 := by
        simp only [mul_assoc]
      _ = t.2.2.1.1 * factorLabel (wordFactors (V * U) L) t.2.2.2.1 *
          t.2.2.2.2.1 := by rw [ih]
      _ = factorLabel (wordFactors (U * V) (L + 1)) w :=
        (peelRow_label U V L i j w).symm

/-- The complete source triangle preserves the ordered total label. -/
theorem psi0_label [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i j : Fin n) (p : ChainBoundary c i j) :
    factorLabel (wordFactors A L) (psi0 c i j p) =
      factorLabel (forwardFactors c) p.2.1 * factorLabel (backwardFactors c) p.2.2 := by
  exact (psi0_inv_label c i j (psi0 c i j p)).symm.trans
    (congrArg (fun q : ChainBoundary c i j => factorLabel (forwardFactors c) q.2.1 *
      factorLabel (backwardFactors c) q.2.2) ((psi0 c i j).symm_apply_apply p))

private theorem localSweep_label [LinearOrder H] {n k : ℕ}
    (U : GroupMat H n k) (V : GroupMat H k n) (i : Fin n) (j : Fin k)
    (p : Σ x : Fin n, At (U * V) i x × At U x j) :
    (localSweep U V i j p).2.1.1 * (localSweep U V i j p).2.2.1 =
      p.2.1.1 * p.2.2.1 := by
  let d := orderedAtEquiv U V i p.1 p.2.1
  change d.2.1.1 * ((orderedAtEquiv V U d.1 j).symm ⟨p.1, d.2.2, p.2.2⟩).1 =
    p.2.1.1 * p.2.2.1
  rw [orderedAt_inv_label, ← mul_assoc, orderedAt_label]

/-- The complete forward sweep preserves the ordered total label. -/
theorem phiR_label [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i : Fin n) (j : Fin m)
    (p : Σ x : Fin n, At A i x × FactorPath (forwardFactors c) x j) :
    factorLabel (forwardFactors c) (phiR c i j p).2.1 * (phiR c i j p).2.2.1 =
      p.2.1.1 * factorLabel (forwardFactors c) p.2.2 := by
  induction c with
  | nil A =>
    rcases p with ⟨x, a, ⟨⟨v, hvx, hvj⟩⟩⟩
    subst v
    subst x
    change 1 * a.1 = a.1 * 1
    simp
  | @cons n k m L A B C U V hA hB c ih =>
    subst A
    subst B
    let f := pathHeadEquiv U (forwardFactors c) p.1 j p.2.2
    let q := localSweep U V i f.1 ⟨p.1, p.2.1, f.2.1⟩
    let t := phiR c q.1 j ⟨f.1, q.2.2, f.2.2⟩
    change (q.2.1.1 * factorLabel (forwardFactors c) t.2.1) * t.2.2.1 =
      p.2.1.1 * (f.2.1.1 * factorLabel (forwardFactors c) f.2.2)
    calc
      (q.2.1.1 * factorLabel (forwardFactors c) t.2.1) * t.2.2.1 =
          q.2.1.1 * (factorLabel (forwardFactors c) t.2.1 * t.2.2.1) := mul_assoc _ _ _
      _ = q.2.1.1 * (q.2.2.1 * factorLabel (forwardFactors c) f.2.2) := by rw [ih]
      _ = (q.2.1.1 * q.2.2.1) * factorLabel (forwardFactors c) f.2.2 :=
        (mul_assoc _ _ _).symm
      _ = (p.2.1.1 * f.2.1.1) * factorLabel (forwardFactors c) f.2.2 := by
        rw [localSweep_label]
      _ = p.2.1.1 * (f.2.1.1 * factorLabel (forwardFactors c) f.2.2) := mul_assoc _ _ _

private theorem pathAt_label [LinearOrder H] {n m L : ℕ}
    (f : Factors H n m L) (i : Fin n) (j : Fin m) (p : At (factorProduct f) i j) :
    factorLabel f (pathAtEquiv f i j p) = p.1 :=
  (rankedFiberEquiv f i j p.1 p.2).property

/-- The same global R/S ranks preserve the source triangle's ordered labels. -/
theorem matrixPsi0_label [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i j : Fin n) (p : Σ v : Fin m, At (R c) i v × At (S c) v j) :
    factorLabel (wordFactors A L) (matrixPsi0 c i j p) = p.2.1.1 * p.2.2.1 := by
  change factorLabel (wordFactors A L) (psi0 c i j _) = _
  rw [psi0_label]
  change factorLabel (forwardFactors c) (pathAtEquiv (forwardFactors c) i p.1 p.2.1) *
    factorLabel (backwardFactors c) (pathAtEquiv (backwardFactors c) p.1 j p.2.2) = _
  rw [pathAt_label, pathAt_label]

/-- Both R occurrences retain their global-rank labels through the sweep. -/
theorem matrixPhiR_label [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i : Fin n) (j : Fin m) (p : Σ x : Fin n, At A i x × At (R c) x j) :
    (matrixPhiR c i j p).2.1.1 * (matrixPhiR c i j p).2.2.1 = p.2.1.1 * p.2.2.1 := by
  let t := phiR c i j ⟨p.1, p.2.1, pathAtEquiv (forwardFactors c) p.1 j p.2.2⟩
  have h := pathAt_label (forwardFactors c) i t.1
    ((pathAtEquiv (forwardFactors c) i t.1).symm t.2.1)
  simp only [Equiv.apply_symm_apply] at h
  change ((pathAtEquiv (forwardFactors c) i t.1).symm t.2.1).1 * t.2.2.1 = _
  rw [← h, phiR_label]
  change p.2.1.1 * factorLabel (forwardFactors c)
    (pathAtEquiv (forwardFactors c) p.1 j p.2.2) = _
  rw [pathAt_label]

private theorem psi0_transport_label [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (f : Factors H n m L) (g : Factors H m n L)
    (hf : forwardFactors c = f) (hg : backwardFactors c = g)
    (i j : Fin n) (p : Σ v : Fin m, FactorPath f i v × FactorPath g v j) :
    factorLabel (wordFactors A L) (psi0 c i j
      (Equiv.cast (by rw [ChainBoundary, hf, hg]) p)) =
        factorLabel f p.2.1 * factorLabel g p.2.2 := by
  cases hf
  cases hg
  exact psi0_label c i j p

/-- The actual terminal triangle preserves the same ordered total label. -/
theorem psiL_label [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i j : Fin m)
    (p : Σ v : Fin n, FactorPath (backwardFactors c) i v × FactorPath (forwardFactors c) v j) :
    factorLabel (wordFactors B L) (psiL c i j p) =
      factorLabel (backwardFactors c) p.2.1 * factorLabel (forwardFactors c) p.2.2 :=
  psi0_transport_label (reverseChain c) (backwardFactors c) (forwardFactors c)
    (reverse_forward c) (reverse_backward c) i j p

private theorem phiR_transport_label [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (f : Factors H n m L) (hf : forwardFactors c = f) (i : Fin n) (j : Fin m)
    (p : Σ x : Fin n, At A i x × FactorPath f x j) :
    let q : Σ y : Fin m, FactorPath f i y × At B y j :=
      Equiv.cast (by rw [hf]) (phiR c i j (Equiv.cast (by rw [hf]) p))
    factorLabel f q.2.1 * q.2.2.1 = p.2.1.1 * factorLabel f p.2.2 := by
  cases hf
  exact phiR_label c i j p

/-- The actual decreasing-layer sweep preserves the ordered total label. -/
theorem phiS_label [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i : Fin m) (j : Fin n)
    (p : Σ x : Fin m, At B i x × FactorPath (backwardFactors c) x j) :
    factorLabel (backwardFactors c) (phiS c i j p).2.1 * (phiS c i j p).2.2.1 =
      p.2.1.1 * factorLabel (backwardFactors c) p.2.2 :=
  phiR_transport_label (reverseChain c) (backwardFactors c) (reverse_forward c) i j p

/-- Both terminal-triangle ranks preserve the ordered labels. -/
theorem matrixPsiL_label [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i j : Fin m) (p : Σ v : Fin n, At (S c) i v × At (R c) v j) :
    factorLabel (wordFactors B L) (matrixPsiL c i j p) = p.2.1.1 * p.2.2.1 := by
  change factorLabel (wordFactors B L) (psiL c i j _) = _
  rw [psiL_label]
  change factorLabel (backwardFactors c) (pathAtEquiv (backwardFactors c) i p.1 p.2.1) *
    factorLabel (forwardFactors c) (pathAtEquiv (forwardFactors c) p.1 j p.2.2) = _
  rw [pathAt_label, pathAt_label]

/-- Both S occurrences preserve the global-rank labels through the dual sweep. -/
theorem matrixPhiS_label [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i : Fin m) (j : Fin n) (p : Σ x : Fin m, At B i x × At (S c) x j) :
    (matrixPhiS c i j p).2.1.1 * (matrixPhiS c i j p).2.2.1 = p.2.1.1 * p.2.2.1 := by
  let t := phiS c i j ⟨p.1, p.2.1, pathAtEquiv (backwardFactors c) p.1 j p.2.2⟩
  have h := pathAt_label (backwardFactors c) i t.1
    ((pathAtEquiv (backwardFactors c) i t.1).symm t.2.1)
  simp only [Equiv.apply_symm_apply] at h
  change ((pathAtEquiv (backwardFactors c) i t.1).symm t.2.1).1 * t.2.2.1 = _
  rw [← h, phiS_label]
  change p.2.1.1 * factorLabel (backwardFactors c)
    (pathAtEquiv (backwardFactors c) p.1 j p.2.2) = _
  rw [pathAt_label]

/-- Evaluate one literal G34 row, keeping its prescribed rightmost U edge. -/
noncomputable def layerSweep [LinearOrder H] {n m : ℕ}
    (U : GroupMat H n m) (V : GroupMat H m n) :
    (l : ℕ) → (i : Fin n) → (j : Fin m) →
      (Σ x : Fin n, Word (U * V) l i x × At U x j) ≃
        Σ y : Fin m, At U i y × Word (V * U) l y j
  | 0, i, j => by
    let left : (Σ x : Fin n, Word (U * V) 0 i x × At U x j) ≃
        At U i j := {
      toFun := fun p => (p.2.1.down.property.1.symm.trans
        p.2.1.down.property.2).symm ▸ p.2.2
      invFun := fun p => ⟨i, nilPath i, p⟩
      left_inv := by
        rintro ⟨x, ⟨⟨v, hvi, hvx⟩⟩, p⟩
        subst v
        subst x
        rfl
      right_inv := fun _ => rfl }
    let right : (Σ y : Fin m, At U i y × Word (V * U) 0 y j) ≃
        At U i j := {
      toFun := fun p => (p.2.2.down.property.1.symm.trans
        p.2.2.down.property.2) ▸ p.2.1
      invFun := fun p => ⟨j, p, nilPath j⟩
      left_inv := by
        rintro ⟨y, p, ⟨⟨v, hvy, hvj⟩⟩⟩
        subst v
        subst y
        rfl
      right_inv := fun _ => rfl }
    exact left.trans right.symm
  | l + 1, i, j => by
    let before : (Σ x : Fin n,
        (Σ v : Fin n, At (U * V) i v × Word (U * V) l v x) ×
          At U x j) ≃
        Σ v : Fin n, At (U * V) i v ×
          (Σ x : Fin n, Word (U * V) l v x × At U x j) := {
      toFun := fun p => ⟨p.2.1.1, p.2.1.2.1, p.1, p.2.1.2.2, p.2.2⟩
      invFun := fun p => ⟨p.2.2.1, ⟨p.1, p.2.1, p.2.2.2.1⟩, p.2.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    let middle : (Σ v : Fin n, At (U * V) i v ×
        (Σ y : Fin m, At U v y × Word (V * U) l y j)) ≃
        Σ y : Fin m, (Σ v : Fin n, At (U * V) i v × At U v y) ×
          Word (V * U) l y j := {
      toFun := fun p => ⟨p.2.2.1, ⟨p.1, p.2.1, p.2.2.2.1⟩, p.2.2.2.2⟩
      invFun := fun p => ⟨p.2.1.1, p.2.1.2.1, p.1, p.2.1.2.2, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    let after : (Σ y : Fin m,
        (Σ z : Fin m, At U i z × At (V * U) z y) × Word (V * U) l y j) ≃
        Σ z : Fin m, At U i z ×
          (Σ y : Fin m, At (V * U) z y × Word (V * U) l y j) := {
      toFun := fun p => ⟨p.2.1.1, p.2.1.2.1, p.1, p.2.1.2.2, p.2.2⟩
      invFun := fun p => ⟨p.2.2.1, ⟨p.1, p.2.1, p.2.2.2.1⟩, p.2.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Equiv.sigmaCongrRight fun x => Equiv.prodCongr
      (pathHeadEquiv (U * V) (wordFactors (U * V) l) i x) (Equiv.refl _)).trans
        (before.trans ((Equiv.sigmaCongrRight fun v => Equiv.prodCongr
          (Equiv.refl _) (layerSweep U V l v j)).trans
            (middle.trans ((Equiv.sigmaCongrRight fun y => Equiv.prodCongr
              (localSweep U V i y) (Equiv.refl _)).trans
                (after.trans (Equiv.sigmaCongrRight fun z => Equiv.prodCongr
                  (Equiv.refl _) (pathHeadEquiv (V * U) (wordFactors (V * U) l) z j).symm))))))

/-- Remove a named nil segment at the end of an arbitrary actual path. -/
private def pathRightNilEquiv {n m L : ℕ} (f : Factors H n m L) (i : Fin n) (j : Fin m) :
    (Σ v : Fin m, FactorPath f i v × FactorPath (Factors.nil (H := H) m) v j) ≃
      FactorPath f i j where
  toFun p := (p.2.2.down.property.1.symm.trans p.2.2.down.property.2) ▸ p.2.1
  invFun p := ⟨j, p, nilPath j⟩
  left_inv p := by
    rcases p with ⟨v, p, ⟨⟨w, hwv, hwj⟩⟩⟩
    subst w
    subst v
    rfl
  right_inv _ := rfl

/-- Remove a named nil segment at the beginning of an arbitrary actual path. -/
private def pathLeftNilEquiv {n m L : ℕ} (f : Factors H n m L) (i : Fin n) (j : Fin m) :
    (Σ v : Fin n, FactorPath (Factors.nil (H := H) n) i v × FactorPath f v j) ≃
      FactorPath f i j where
  toFun p := (p.2.1.down.property.1.symm.trans p.2.1.down.property.2).symm ▸ p.2.2
  invFun p := ⟨i, nilPath i, p⟩
  left_inv p := by
    rcases p with ⟨v, ⟨⟨w, hwi, hwv⟩⟩, p⟩
    subst w
    subst v
    rfl
  right_inv _ := rfl

/-- Evaluate the rectangle row by row on this same retained chain. -/
noncomputable def rowFirst [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L) (l : ℕ)
    (i : Fin n) (j : Fin m) :
    (Σ x : Fin n, Word A l i x × FactorPath (forwardFactors c) x j) ≃
      Σ y : Fin m, FactorPath (forwardFactors c) i y × Word B l y j := by
  induction c with
  | @nil n A =>
    exact (pathRightNilEquiv (wordFactors A l) i j).trans
      (pathLeftNilEquiv (wordFactors A l) i j).symm
  | @cons n k m L A B C U V hA hB c ih =>
    subst A
    subst B
    let before : (Σ x : Fin n, Word (U * V) l i x ×
        (Σ z : Fin k, At U x z × FactorPath (forwardFactors c) z j)) ≃
        Σ z : Fin k, (Σ x : Fin n, Word (U * V) l i x × At U x z) ×
          FactorPath (forwardFactors c) z j := {
      toFun := fun p => ⟨p.2.2.1, ⟨p.1, p.2.1, p.2.2.2.1⟩, p.2.2.2.2⟩
      invFun := fun p => ⟨p.2.1.1, p.2.1.2.1, p.1, p.2.1.2.2, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    let middle : (Σ z : Fin k, (Σ y : Fin k, At U i y × Word (V * U) l y z) ×
        FactorPath (forwardFactors c) z j) ≃
        Σ y : Fin k, At U i y ×
          (Σ z : Fin k, Word (V * U) l y z × FactorPath (forwardFactors c) z j) := {
      toFun := fun p => ⟨p.2.1.1, p.2.1.2.1, p.1, p.2.1.2.2, p.2.2⟩
      invFun := fun p => ⟨p.2.2.1, ⟨p.1, p.2.1, p.2.2.2.1⟩, p.2.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    let after : (Σ y : Fin k, At U i y ×
        (Σ z : Fin m, FactorPath (forwardFactors c) y z × Word C l z j)) ≃
        Σ z : Fin m, (Σ y : Fin k, At U i y × FactorPath (forwardFactors c) y z) ×
          Word C l z j := {
      toFun := fun p => ⟨p.2.2.1, ⟨p.1, p.2.1, p.2.2.2.1⟩, p.2.2.2.2⟩
      invFun := fun p => ⟨p.2.1.1, p.2.1.2.1, p.1, p.2.1.2.2, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Equiv.sigmaCongrRight fun x => Equiv.prodCongr (Equiv.refl _)
      (pathHeadEquiv U (forwardFactors c) x j)).trans
        (before.trans ((Equiv.sigmaCongrRight fun z =>
          Equiv.prodCongr (layerSweep U V l i z) (Equiv.refl _)).trans
            (middle.trans ((Equiv.sigmaCongrRight fun y =>
              Equiv.prodCongr (Equiv.refl _) (ih y j)).trans
                (after.trans (Equiv.sigmaCongrRight fun z =>
                  Equiv.prodCongr (pathHeadEquiv U (forwardFactors c) i z).symm
                    (Equiv.refl _)))))))

structure NumberedRow {n : ℕ} (A : GroupMat H n n) (l : ℕ) where
  vertex : Fin (l + 1) → Fin n
  edge : (i : Fin l) → At A (vertex i.castSucc) (vertex i.succ)

/-- The U half-edges of a row, including its prescribed last boundary edge. -/
noncomputable def rowHalves [LinearOrder H] {n k l : ℕ}
    (U : GroupMat H n k) (V : GroupMat H k n)
    (r : NumberedRow (U * V) l) (z : Fin k)
    (right : At U (r.vertex (Fin.last l)) z) :
    (i : Fin (l + 1)) → Σ y : Fin k, At U (r.vertex i) y :=
  fun i => if hi : i.val < l then
    let t : Fin l := ⟨i.val, hi⟩
    let p := orderedAtEquiv U V (r.vertex t.castSucc) (r.vertex t.succ) (r.edge t)
    ⟨p.1, p.2.1⟩
  else
    have he : i = Fin.last l := Fin.ext (by change i.val = l; omega)
    ⟨z, he.symm ▸ right⟩

private theorem rowHalves_at [LinearOrder H] {n k l : ℕ}
    (U : GroupMat H n k) (V : GroupMat H k n)
    (r : NumberedRow (U * V) l) (z : Fin k)
    (right : At U (r.vertex (Fin.last l)) z) (i : Fin l) :
    rowHalves U V r z right i.castSucc =
      ⟨(orderedAtEquiv U V _ _ (r.edge i)).1,
        (orderedAtEquiv U V _ _ (r.edge i)).2.1⟩ := by
  unfold rowHalves
  split
  · rfl
  · rename_i hi
    exact False.elim (hi i.isLt)

private theorem rowHalves_right [LinearOrder H] {n k l : ℕ}
    (U : GroupMat H n k) (V : GroupMat H k n)
    (r : NumberedRow (U * V) l) (z : Fin k)
    (right : At U (r.vertex (Fin.last l)) z) :
    rowHalves U V r z right (Fin.last l) = ⟨z, right⟩ := by
  unfold rowHalves
  split
  · rename_i h
    exact False.elim (Nat.lt_irrefl l h)
  · rfl

/-- One G34 row is generated by theta splitting and eta joining at literal indices. -/
noncomputable def nextNumberedRow [LinearOrder H] {n k l : ℕ}
    (U : GroupMat H n k) (V : GroupMat H k n)
    (r : NumberedRow (U * V) l) (z : Fin k)
    (right : At U (r.vertex (Fin.last l)) z) : NumberedRow (V * U) l where
  vertex i := (rowHalves U V r z right i).1
  edge i := by
    let p := orderedAtEquiv U V (r.vertex i.castSucc) (r.vertex i.succ) (r.edge i)
    let v : At V (rowHalves U V r z right i.castSucc).1 (r.vertex i.succ) :=
      (congrArg (fun h => At V h.1 (r.vertex i.succ))
        (rowHalves_at U V r z right i)).symm ▸ p.2.2
    exact (orderedAtEquiv V U _ _).symm
      ⟨r.vertex i.succ, v, (rowHalves U V r z right i.succ).2⟩

/-- A generated row, its half-edges, and the two literal recurrence laws. -/
structure G34Step [LinearOrder H] {n k l : ℕ}
    (A : GroupMat H n n) (B : GroupMat H k k)
    (U : GroupMat H n k) (V : GroupMat H k n)
    (hA : A = U * V) (hB : B = V * U) (r : NumberedRow A l) where
  next : NumberedRow B l
  u : (i : Fin (l + 1)) → At U (r.vertex i) (next.vertex i)
  v : (i : Fin l) → At V (next.vertex i.castSucc) (r.vertex i.succ)
  theta : ∀ i, orderedAtEquiv U V _ _
    (Equiv.cast (congrArg (fun M => At M (r.vertex i.castSucc) (r.vertex i.succ)) hA)
      (r.edge i)) = ⟨next.vertex i.castSucc, u i.castSucc, v i⟩
  eta : ∀ i, Equiv.cast (congrArg
    (fun M => At M (next.vertex i.castSucc) (next.vertex i.succ)) hB) (next.edge i) =
    (orderedAtEquiv V U _ _).symm ⟨r.vertex i.succ, v i, u i.succ⟩

/-- Generate one row without discarding any independent half-edge copy. -/
noncomputable def generateG34Step [LinearOrder H] {n k l : ℕ}
    (A : GroupMat H n n) (B : GroupMat H k k)
    (U : GroupMat H n k) (V : GroupMat H k n)
    (hA : A = U * V) (hB : B = V * U) (r : NumberedRow A l)
    (z : Fin k) (right : At U (r.vertex (Fin.last l)) z) : G34Step A B U V hA hB r := by
  subst A
  subst B
  let halves := rowHalves U V r z right
  let vs (i : Fin l) : At V (halves i.castSucc).1 (r.vertex i.succ) :=
    (congrArg (fun h => At V h.1 (r.vertex i.succ))
      (rowHalves_at U V r z right i)).symm ▸
        (orderedAtEquiv U V _ _ (r.edge i)).2.2
  exact {
    next := nextNumberedRow U V r z right
    u := fun i => (halves i).2
    v := vs
    theta := by
      intro i
      have transport (p : Σ y : Fin k, At U (r.vertex i.castSucc) y ×
          At V y (r.vertex i.succ))
          (h : Σ y : Fin k, At U (r.vertex i.castSucc) y)
          (he : h = ⟨p.1, p.2.1⟩) :
          p = ⟨h.1, h.2, (congrArg (fun t => At V t.1 (r.vertex i.succ)) he).symm ▸
            p.2.2⟩ := by
        cases he
        rfl
      exact transport (orderedAtEquiv U V _ _ (r.edge i)) (halves i.castSucc)
        (rowHalves_at U V r z right i)
    eta := fun _ => rfl }

private theorem generateG34Step_right [LinearOrder H] {n k l : ℕ}
    (A : GroupMat H n n) (B : GroupMat H k k)
    (U : GroupMat H n k) (V : GroupMat H k n)
    (hA : A = U * V) (hB : B = V * U) (r : NumberedRow A l)
    (z : Fin k) (right : At U (r.vertex (Fin.last l)) z) :
    (generateG34Step A B U V hA hB r z right).next.vertex (Fin.last l) = z := by
  subst A
  subst B
  exact congrArg Sigma.fst (rowHalves_right U V r z right)

private theorem generateG34Step_right_u [LinearOrder H] {n k l : ℕ}
    (A : GroupMat H n n) (B : GroupMat H k k)
    (U : GroupMat H n k) (V : GroupMat H k n)
    (hA : A = U * V) (hB : B = V * U) (r : NumberedRow A l)
    (z : Fin k) (right : At U (r.vertex (Fin.last l)) z) :
    HEq ((generateG34Step A B U V hA hB r z right).u (Fin.last l)) right := by
  subst A
  subst B
  have snd_heq (a b : Σ y : Fin k, At U (r.vertex (Fin.last l)) y) (h : a = b) :
      HEq a.2 b.2 := by
    cases h
    rfl
  exact snd_heq _ _ (rowHalves_right U V r z right)

/-- The full array has literal row and column indices and the actual source telescope. -/
structure G34Array [LinearOrder H] {L : ℕ} (data : IndexedChain H L) (l : ℕ) where
  row : (j : Fin (L + 1)) → NumberedRow (data.A j) l
  step : (j : Fin L) → G34Step (data.A j.castSucc) (data.A j.succ)
    (data.U j) (data.V j) (data.leftFactor j) (data.rightFactor j) (row j.castSucc)
  nextRow : ∀ j, (step j).next = row j.succ

/-- Fill the same array row by row from its top row and prescribed right boundary. -/
noncomputable def generateG34 [LinearOrder H] : {L : ℕ} → (data : IndexedChain H L) →
    (l : ℕ) → (b : (j : Fin (L + 1)) → Fin (data.d j)) →
    (rin : (j : Fin L) → At (data.U j) (b j.castSucc) (b j.succ)) →
    (r : NumberedRow (data.A 0) l) → (hr : r.vertex (Fin.last l) = b 0) →
    {g : G34Array data l // g.row 0 = r ∧
      (∀ j, (g.row j).vertex (Fin.last l) = b j) ∧
      ∀ j, HEq ((g.step j).u (Fin.last l)) (rin j)}
  | 0, data, l, b, _rin, r, hr => by
    let rows : (j : Fin 1) → NumberedRow (data.A j) l :=
      Fin.cases r (fun j => Fin.elim0 j)
    exact ⟨⟨rows, (fun j => Fin.elim0 j), (fun j => Fin.elim0 j)⟩, rfl,
      (fun j => Fin.cases hr (fun k => Fin.elim0 k) j), (fun j => Fin.elim0 j)⟩
  | L + 1, data, l, b, rin, r, hr => by
    let right : At (data.U 0) (r.vertex (Fin.last l)) (b 1) := hr.symm ▸ rin 0
    let s := generateG34Step (data.A 0) (data.A 1) (data.U 0) (data.V 0)
      (data.leftFactor 0) (data.rightFactor 0) r (b 1) right
    let t := generateG34 (tail data) l (fun j => b j.succ) (fun j => rin j.succ)
      s.next (generateG34Step_right _ _ _ _ _ _ _ _ _)
    let rows : (j : Fin (L + 2)) → NumberedRow (data.A j) l := Fin.cases r t.val.row
    let steps : (j : Fin (L + 1)) → G34Step (data.A j.castSucc) (data.A j.succ)
        (data.U j) (data.V j) (data.leftFactor j) (data.rightFactor j) (rows j.castSucc) :=
      Fin.cases s t.val.step
    refine ⟨⟨rows, steps, ?_⟩, rfl, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun k => t.val.nextRow k) j
      exact t.property.1.symm
    · intro j
      exact Fin.cases hr (fun k => t.property.2.1 k) j
    · intro j
      refine Fin.cases ?_ (fun k => t.property.2.2 k) j
      exact (generateG34Step_right_u _ _ _ _ _ _ _ _ _).trans
        (eqRec_heq (φ := fun x => At (data.U 0) x (b 1)) hr.symm (rin 0))

/-- The local recurrence uniquely determines a row when its last U edge is fixed. -/
theorem g34Step_unique [LinearOrder H] {n k l : ℕ}
    (A : GroupMat H n n) (B : GroupMat H k k)
    (U : GroupMat H n k) (V : GroupMat H k n)
    (hA : A = U * V) (hB : B = V * U) (r : NumberedRow A l)
    (p q : G34Step A B U V hA hB r)
    (hvlast : p.next.vertex (Fin.last l) = q.next.vertex (Fin.last l))
    (hulast : HEq (p.u (Fin.last l)) (q.u (Fin.last l))) : p = q := by
  rcases p with ⟨⟨xp, ap⟩, up, vp, tp, ep⟩
  rcases q with ⟨⟨xq, aq⟩, uq, vq, tq, eq⟩
  have hx : xp = xq := by
    funext i
    refine Fin.lastCases hvlast (fun t => ?_) i
    exact congrArg Sigma.fst ((tp t).symm.trans (tq t))
  cases hx
  have huv (i : Fin l) : (up i.castSucc, vp i) = (uq i.castSucc, vq i) := by
    have h := (tp i).symm.trans (tq i)
    exact eq_of_heq (Sigma.mk.inj h).2
  have hu : up = uq := by
    funext i
    exact Fin.lastCases (eq_of_heq hulast)
      (fun t => congrArg Prod.fst (huv t)) i
  have hv : vp = vq := by
    funext i
    exact congrArg Prod.snd (huv i)
  cases hu
  cases hv
  have ha : ap = aq := by
    funext i
    exact (Equiv.cast _).injective ((ep i).trans (eq i).symm)
  cases ha
  rfl

private theorem step_cast_next [LinearOrder H] {n k l : ℕ}
    {A : GroupMat H n n} {B : GroupMat H k k}
    {U : GroupMat H n k} {V : GroupMat H k n}
    {hA : A = U * V} {hB : B = V * U} {r s : NumberedRow A l}
    (h : r = s) (p : G34Step A B U V hA hB r) :
    (h ▸ p : G34Step A B U V hA hB s).next = p.next := by
  cases h
  rfl

private theorem step_cast_u [LinearOrder H] {n k l : ℕ}
    {A : GroupMat H n n} {B : GroupMat H k k}
    {U : GroupMat H n k} {V : GroupMat H k n}
    {hA : A = U * V} {hB : B = V * U} {r s : NumberedRow A l}
    (h : r = s) (p : G34Step A B U V hA hB r) (i : Fin (l + 1)) :
    HEq ((h ▸ p : G34Step A B U V hA hB s).u i) (p.u i) := by
  cases h
  rfl

private theorem array_next_unique [LinearOrder H] {L l : ℕ} {data : IndexedChain H L}
    (p q : G34Array data l) (j : Fin L) (htop : p.row j.castSucc = q.row j.castSucc)
    (hlast : (p.row j.succ).vertex (Fin.last l) = (q.row j.succ).vertex (Fin.last l))
    (hu : HEq ((p.step j).u (Fin.last l)) ((q.step j).u (Fin.last l))) :
    p.row j.succ = q.row j.succ := by
  let q' := (htop.symm ▸ q.step j : G34Step _ _ _ _ _ _ (p.row j.castSucc))
  have hnext : q'.next = (q.step j).next := step_cast_next htop.symm (q.step j)
  have hvertex : (p.step j).next.vertex (Fin.last l) = q'.next.vertex (Fin.last l) := by
    rw [hnext, p.nextRow j, q.nextRow j]
    exact hlast
  have hu' : HEq ((p.step j).u (Fin.last l)) (q'.u (Fin.last l)) :=
    hu.trans (step_cast_u htop.symm (q.step j) (Fin.last l)).symm
  have hs := g34Step_unique _ _ _ _ _ _ _ (p.step j) q' hvertex hu'
  have hn := congrArg G34Step.next hs
  rw [hnext, p.nextRow j, q.nextRow j] at hn
  exact hn

/-- Top and prescribed right boundary determine the entire actual finite G34 array. -/
theorem g34Array_unique [LinearOrder H] {L l : ℕ} {data : IndexedChain H L}
    (p q : G34Array data l) (htop : p.row 0 = q.row 0)
    (hlast : ∀ j, (p.row j).vertex (Fin.last l) = (q.row j).vertex (Fin.last l))
    (hu : ∀ j, HEq ((p.step j).u (Fin.last l)) ((q.step j).u (Fin.last l))) : p = q := by
  have hr : ∀ j, p.row j = q.row j :=
    Fin.induction htop (fun j ih => array_next_unique p q j ih (hlast j.succ) (hu j))
  rcases p with ⟨rp, sp, hp⟩
  rcases q with ⟨rq, sq, hq⟩
  have he : rp = rq := funext hr
  cases he
  have hs : sp = sq := by
    funext j
    apply g34Step_unique
    · rw [hp j, hq j]
    · exact hu j
  cases hs
  rfl

/-- Read an actual finite row as its complete typed word. -/
def rowWord {n : ℕ} (A : GroupMat H n n) : (l : ℕ) → (r : NumberedRow A l) →
    Word A l (r.vertex 0) (r.vertex (Fin.last l))
  | 0, r => nilPath (r.vertex 0)
  | l + 1, r =>
    ⟨r.vertex 1, (r.edge 0).1, (r.edge 0).2,
      rowWord A l ⟨(fun i => r.vertex i.succ), (fun i => r.edge i.succ)⟩⟩

def rowTail {n l : ℕ} {A : GroupMat H n n} (r : NumberedRow A (l + 1)) :
    NumberedRow A l where
  vertex i := r.vertex i.succ
  edge i := r.edge i.succ

def stepTail [LinearOrder H] {n k l : ℕ}
    {A : GroupMat H n n} {B : GroupMat H k k}
    {U : GroupMat H n k} {V : GroupMat H k n}
    {hA : A = U * V} {hB : B = V * U} {r : NumberedRow A (l + 1)}
    (p : G34Step A B U V hA hB r) : G34Step A B U V hA hB (rowTail r) where
  next := rowTail p.next
  u i := p.u i.succ
  v i := p.v i.succ
  theta i := p.theta i.succ
  eta i := p.eta i.succ

private theorem g34_cell [LinearOrder H] {n k l : ℕ}
    (U : GroupMat H n k) (V : GroupMat H k n) (r : NumberedRow (U * V) l)
    (p : G34Step (U * V) (V * U) U V rfl rfl r) (i : Fin l) :
    localSweep U V (r.vertex i.castSucc) (p.next.vertex i.succ)
      ⟨r.vertex i.succ, r.edge i, p.u i.succ⟩ =
      ⟨p.next.vertex i.castSucc, p.u i.castSucc, p.next.edge i⟩ := by
  have ht := p.theta i
  have he := p.eta i
  change orderedAtEquiv U V _ _ (r.edge i) =
    ⟨p.next.vertex i.castSucc, p.u i.castSucc, p.v i⟩ at ht
  change p.next.edge i = (orderedAtEquiv V U _ _).symm
    ⟨r.vertex i.succ, p.v i, p.u i.succ⟩ at he
  change (let q := orderedAtEquiv U V _ _ (r.edge i);
    (⟨q.1, q.2.1, (orderedAtEquiv V U _ _).symm
      ⟨r.vertex i.succ, q.2.2, p.u i.succ⟩⟩ :
        Σ y : Fin k, At U (r.vertex i.castSucc) y × At (V * U) y (p.next.vertex i.succ))) = _
  rw [ht]
  dsimp only
  rw [← he]

attribute [local irreducible] layerSweep localSweep

/-- The row sweep evaluates every literal cell of the same generated row. -/
theorem g34_layerSweep [LinearOrder H] {n k l : ℕ}
    (U : GroupMat H n k) (V : GroupMat H k n) (r : NumberedRow (U * V) l)
    (p : G34Step (U * V) (V * U) U V rfl rfl r) :
    layerSweep U V l (r.vertex 0) (p.next.vertex (Fin.last l))
      ⟨r.vertex (Fin.last l), rowWord (U * V) l r, p.u (Fin.last l)⟩ =
      ⟨p.next.vertex 0, p.u 0, rowWord (V * U) l p.next⟩ := by
  induction l with
  | zero =>
    unfold layerSweep
    rfl
  | succ l ih =>
    let finish (t : Σ y : Fin k, At U (r.vertex 1) y ×
        Word (V * U) l y (p.next.vertex (Fin.last (l + 1)))) :
        Σ y : Fin k, At U (r.vertex 0) y ×
          Word (V * U) (l + 1) y (p.next.vertex (Fin.last (l + 1))) :=
      let q := localSweep U V (r.vertex 0) t.1 ⟨r.vertex 1, r.edge 0, t.2.1⟩
      ⟨q.1, q.2.1, ⟨t.1, q.2.2.1, q.2.2.2, t.2.2⟩⟩
    conv_lhs => unfold layerSweep
    change finish
      (layerSweep U V l (r.vertex 1) (p.next.vertex (Fin.last (l + 1)))
        ⟨r.vertex (Fin.last (l + 1)), rowWord (U * V) l (rowTail r),
          p.u (Fin.last (l + 1))⟩) = _
    refine ((congrArg finish (ih (rowTail r) (stepTail p))).trans ?_)
    let append (q : Σ y : Fin k, At U (r.vertex 0) y × At (V * U) y (p.next.vertex 1)) :
        Σ y : Fin k, At U (r.vertex 0) y ×
          Word (V * U) (l + 1) y (p.next.vertex (Fin.last (l + 1))) :=
      ⟨q.1, q.2.1, ⟨p.next.vertex 1, q.2.2.1, q.2.2.2,
        rowWord (V * U) l (rowTail p.next)⟩⟩
    change append (localSweep U V (r.vertex 0) (p.next.vertex 1)
      ⟨r.vertex 1, r.edge 0, p.u 1⟩) =
        append ⟨p.next.vertex 0, p.u 0, p.next.edge 0⟩
    exact congrArg append (g34_cell U V r p 0)

/-- The tail is the actual subarray with the first source layer removed. -/
def arrayTail [LinearOrder H] {L l : ℕ} {data : IndexedChain H (L + 1)}
    (g : G34Array data l) : G34Array (tail data) l where
  row j := g.row j.succ
  step j := g.step j.succ
  nextRow j := g.nextRow j.succ

/-- Read the literal u_0^0,...,u_0^(L-1) boundary as one actual R path. -/
def arrayLeftPath [LinearOrder H] : {L l : ℕ} → {data : IndexedChain H L} →
    (g : G34Array data l) → FactorPath (forwardFactors (toChain data))
      ((g.row 0).vertex 0) ((g.row (Fin.last L)).vertex 0)
  | 0, _l, _data, g => nilPath ((g.row 0).vertex 0)
  | L + 1, _l, _data, g => by
    let a := g.step 0
    have u : At _ ((g.row 0).vertex 0) ((g.row 1).vertex 0) :=
      congrArg (fun r : NumberedRow (_data.A 1) _l => r.vertex 0) (g.nextRow 0) ▸ a.u 0
    exact ⟨(g.row 1).vertex 0, u.1, u.2, arrayLeftPath (arrayTail g)⟩

/-- The array's actual left factor boundary and bottom row, with their common vertex. -/
def arrayOutput [LinearOrder H] {L l : ℕ} {data : IndexedChain H L}
    (g : G34Array data l) :
    Σ y : Fin (data.d (Fin.last L)),
      FactorPath (forwardFactors (toChain data)) ((g.row 0).vertex 0) y ×
        Word (data.A (Fin.last L)) l y ((g.row (Fin.last L)).vertex (Fin.last l)) :=
  ⟨(g.row (Fin.last L)).vertex 0, arrayLeftPath g, rowWord _ l (g.row (Fin.last L))⟩

def rowPrefix {n l : ℕ} {A : GroupMat H n n} (r : NumberedRow A (l + 1)) :
    NumberedRow A l where
  vertex i := r.vertex i.castSucc
  edge i := r.edge i.castSucc

private def stepPrefix [LinearOrder H] {n k l : ℕ}
    {A : GroupMat H n n} {B : GroupMat H k k}
    {U : GroupMat H n k} {V : GroupMat H k n}
    {hA : A = U * V} {hB : B = V * U} {r : NumberedRow A (l + 1)}
    (p : G34Step A B U V hA hB r) : G34Step A B U V hA hB (rowPrefix r) where
  next := rowPrefix p.next
  u i := p.u i.castSucc
  v i := p.v i.castSucc
  theta i := p.theta i.castSucc
  eta i := p.eta i.castSucc

def arrayPrefix [LinearOrder H] {L l : ℕ} {data : IndexedChain H L}
    (g : G34Array data (l + 1)) : G34Array data l where
  row j := rowPrefix (g.row j)
  step j := stepPrefix (g.step j)
  nextRow j := congrArg rowPrefix (g.nextRow j)

end D5.S3.ConceptDynamics.Coding.CountedGroupChainPaths
