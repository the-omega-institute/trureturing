/- GID: D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionSignTensor
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/BinaryDeletionSignTensor
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A signed coefficient tensor gives nonzero integer witnesses with zero site deletions. -/

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSignTensor

/-- Agreement of the two bits or one of their two ordered differences. -/
inductive Site where
  | common
  | fromZero
  | fromOne

/-- The three possible coefficients of the integer witness. -/
inductive Sign where
  | zero
  | positive
  | negative

def negate : Sign → Sign
  | .zero => .zero
  | .positive => .negative
  | .negative => .positive

def multiply : Sign → Sign → Sign
  | .zero, _ => .zero
  | .positive, z => z
  | .negative, z => negate z

def asInt : Sign → Int
  | .zero => 0
  | .positive => 1
  | .negative => -1

def localCoefficient (p : Site) (x y : Bool) : Sign :=
  match p with
  | .common => if x then (if y then .negative else .zero)
      else (if y then .zero else .positive)
  | .fromZero => if x then .zero else (if y then .positive else .zero)
  | .fromOne => if x then (if y then .zero else .positive) else .zero

/-- Evaluate the product of the local coefficients on two Boolean words. -/
def coefficient (pattern : List Site) : List Bool → List Bool → Sign :=
  pattern.foldr
    (fun site tail x y =>
      match x with
      | [] => .zero
      | a :: xs =>
        match y with
        | [] => .zero
        | b :: ys => multiply (localCoefficient site a b) (tail xs ys))
    (fun x y => if x.isEmpty && y.isEmpty then .positive else .zero)

private theorem localOpposites (p : Site) (s : Sign) :
    multiply (localCoefficient p true true) s =
      negate (multiply (localCoefficient p false false) s) := by
  cases p <;> rfl

private theorem multiplyNegate (a b : Sign) :
    multiply a (negate b) = negate (multiply a b) := by
  cases a <;> rfl

private theorem deleteSiteSign (before after : List Site) (p : Site) (x y u v : List Bool)
    (hx : x.length = before.length) (hy : y.length = before.length) :
    coefficient (before ++ p :: after) (x ++ true :: u) (y ++ true :: v) =
      negate (coefficient (before ++ p :: after) (x ++ false :: u) (y ++ false :: v)) := by
  induction before generalizing x y with
  | nil =>
    cases x with
    | nil =>
      cases y with
      | nil => exact localOpposites p (coefficient after u v)
      | cons a t => exact False.elim (Nat.noConfusion hy)
    | cons a t => exact False.elim (Nat.noConfusion hx)
  | cons a rest ih =>
    cases x with
    | nil => exact False.elim (Nat.noConfusion hx)
    | cons b x =>
      cases y with
      | nil => exact False.elim (Nat.noConfusion hy)
      | cons c y =>
        let f := multiply (localCoefficient a b c)
        let low := coefficient (rest ++ p :: after) (x ++ false :: u) (y ++ false :: v)
        let high := coefficient (rest ++ p :: after) (x ++ true :: u) (y ++ true :: v)
        change f high = negate (f low)
        exact (congrArg f (ih x y (Nat.succ.inj hx) (Nat.succ.inj hy))).trans
          (multiplyNegate (localCoefficient a b c) low)

private theorem oppositeSum (s : Sign) : asInt s + asInt (negate s) = 0 := by
  cases s <;> decide

/-- Summing over the two insertions at an arbitrary site gives zero. -/
theorem deleteSite (before after : List Site) (p : Site) (x y u v : List Bool)
    (hx : x.length = before.length) (hy : y.length = before.length) :
    asInt (coefficient (before ++ p :: after) (x ++ false :: u) (y ++ false :: v)) +
      asInt (coefficient (before ++ p :: after) (x ++ true :: u) (y ++ true :: v)) = 0 := by
  let low := coefficient (before ++ p :: after) (x ++ false :: u) (y ++ false :: v)
  exact (congrArg (fun s => asInt low + asInt s)
    (deleteSiteSign before after p x y u v hx hy)).trans (oppositeSum low)

def leftBit : Site → Bool
  | .fromOne => true
  | .common | .fromZero => false

def rightBit : Site → Bool
  | .fromZero => true
  | .common | .fromOne => false

/-- The coefficient at the representative with all common bits zero is one. -/
theorem actualEntry (pattern : List Site) :
    coefficient pattern (pattern.map leftBit) (pattern.map rightBit) = .positive := by
  induction pattern with
  | nil => rfl
  | cons site rest ih =>
    cases site <;> exact ih

end D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSignTensor
