/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215Pure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215Pure
   mirror-E: none(waiver:inert-base-history-replay)
   anchors: [mathlib/module/Mathlib.Data.List.GetD]
   utility: none
   digest: Replays pure stack histories above an inert base and characterizes their budget. -/

import Mathlib.Data.List.GetD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215Pure

inductive PureStep where
  | record (gap : ℕ)
  | descend (site : ℕ)

def PureStep.shift (offset : ℕ) : PureStep → PureStep
  | .record gap => .record gap
  | .descend site => .descend (offset + site)

def spend : List PureStep → ℕ
  | [] => 0
  | .record gap :: rest => gap + spend rest
  | .descend _ :: rest => spend rest

inductive PureRun : List Bool → List PureStep → List Bool → Prop where
  | nil (stack : List Bool) : PureRun stack [] stack
  | record (stack ending : List Bool) (rest : List PureStep) (gap : ℕ)
      (tail : PureRun (stack ++ List.replicate gap false ++ [true]) rest ending) :
      PureRun stack (.record gap :: rest) ending
  | descend (stack ending : List Bool) (rest : List PureStep) (site : ℕ)
      (hsite : site < stack.length) (hfresh : stack.getD site true = false)
      (tail : PureRun (stack.take site) rest ending) :
      PureRun stack (.descend site :: rest) ending

inductive BudgetRun : List Bool → ℕ → List PureStep → List Bool → Prop where
  | nil (stack : List Bool) (budget : ℕ) (hbudget : 0 < budget) :
      BudgetRun stack budget [] stack
  | record (stack ending : List Bool) (rest : List PureStep) (gap budget : ℕ)
      (hgap : gap < budget)
      (tail : BudgetRun (stack ++ List.replicate gap false ++ [true]) (budget - gap)
        rest ending) : BudgetRun stack budget (.record gap :: rest) ending
  | descend (stack ending : List Bool) (rest : List PureStep) (site budget : ℕ)
      (hsite : site < stack.length) (hfresh : stack.getD site true = false)
      (tail : BudgetRun (stack.take site) budget rest ending) :
      BudgetRun stack budget (.descend site :: rest) ending

end D5.S3.Combinatorics.WeakAscent.WeakAscent215Pure
