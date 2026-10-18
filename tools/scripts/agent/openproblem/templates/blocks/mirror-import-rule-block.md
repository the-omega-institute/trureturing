
## Import rule (binding, every lane)
A direct import of the module that defines a constant the delivered module uses is correct even when that constant is also reachable transitively ("import where consumed"). A Mathlib import whose single deletion still compiles is not a blocking finding. For `D5.*` imports judge by constant ownership: an import is required exactly when some constant the module uses is defined in the imported module itself; a `D5.*` import used only as a relay for other modules' constants is a blocking finding (the freeze would record a false frozen prerequisite).
