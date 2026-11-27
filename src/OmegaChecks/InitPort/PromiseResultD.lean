module
prelude
public import Init.System.Promise

/-- Compile the pinned macro-inline body, including its synchronous task mapping. -/
@[export omega_pinned_promise_result_d]
public def omegaPromiseResultD {α : Type} (promise : IO.Promise α) (fallback : α) : Task α :=
  promise.resultD fallback
