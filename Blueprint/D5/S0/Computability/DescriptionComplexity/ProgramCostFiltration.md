# Program Cost Filtration

## Abstract

Description length gives finite program sublevels, runtime alone admits infinitely many constant functions, and mixed description-runtime cost is finite again.

**Theorem 1.1 (Description, runtime, and mixed-cost sublevels).**

$$\begin{gathered}\forall Program, Data: \operatorname{Type},\\{}[\operatorname{Infinite}\left(Data\right)],\\{}\forall Q, T: \mathbb{N},\\{}\forall code: Program \to \operatorname{List}\left(\operatorname{Fin}\left(2\right)\right), \forall semantics: Program \to Data \to Data,\\{}\forall runtime: Program \to \mathbb{N}, \forall constantProgram: Data \to Program,\\{}\operatorname{Injective}\left(code\right) \land (\forall c, x: Data, \operatorname{semantics}\left(\operatorname{constantProgram}\left(c\right), x\right) = c) \land (\forall c: Data, \operatorname{runtime}\left(\operatorname{constantProgram}\left(c\right)\right) \leq T) \Rightarrow\\{}\operatorname{Finite}\left(\left\{\operatorname{length}\left(\operatorname{code}\left(p\right)\right) \leq Q \mid p \in Program\right\}\right) \land \operatorname{Infinite}\left(\left\{\exists p: Program, \operatorname{semantics}\left(p\right) = f \land \operatorname{runtime}\left(p\right) \leq T \mid f \in Data \to Data\right\}\right) \land \operatorname{Finite}\left(\left\{\operatorname{length}\left(\operatorname{code}\left(p\right)\right) + \log_{2}(\operatorname{runtime}\left(p\right)) \leq Q \mid p \in Program\right\}\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/DescriptionComplexity/ProgramCostFiltration.program_cost_filtration_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Program is an arbitrary carrier equipped with an injective binary code, a semantic function on Data, and a natural-number runtime. Data is infinite, and constantProgram compiles every constant semantic function within the common runtime budget T.

The first clause pulls the finite set of bounded binary codes back along the injective code. The second clause embeds the infinite Data carrier as pairwise distinct constant functions realized within runtime T. The third clause observes that mixed cost bounds description length.

The logarithmic term is Nat.log with base two. No positivity condition on runtime is needed for the finite-sublevel conclusion, because description length alone is already bounded by the mixed budget.

## References

- Truth anchor: `D5/S0/Computability/DescriptionComplexity/ProgramCostFiltration.program_cost_filtration_classification`
- Dependency: [D5/S0/Asymptotics/FiniteProgramLevelSet](../../Asymptotics/FiniteProgramLevelSet.md)
