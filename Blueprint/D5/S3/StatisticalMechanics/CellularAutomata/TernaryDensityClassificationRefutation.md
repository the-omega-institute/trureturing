# A misclassified configuration for a ternary two-rule density classifier

## Abstract

The ternary cellular automaton with Wolfram number 6478767664173 sends the configuration 210 of length 3 to 111, which it and the rule 7580606234490 both fix, although 210 contains a zero and has density 1/2. This refutes Conjecture 1 of H. Fukś and R. Procyk (arXiv:2002.08924), which asserts that this pair of rules classifies by density every finite configuration containing a zero.

**Definition 1.1 (The local rule of a Wolfram number).**

$$\operatorname{wolfram}\left(N, a, b, c\right) = \left\lfloor\frac{N}{3^{9 \cdot a + 3 \cdot b + c}}\right\rfloor \operatorname{mod} 3$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.wolfram` (`✓ std3`).

*Citation.* Henryk Fukś; Roman Procyk (2019). *Explorations of Ternary Cellular Automata and Ternary Density Classification Problems*. DOI: [10.5506/APhysPolBSupp.12.75](https://doi.org/10.5506/APhysPolBSupp.12.75). URL: <https://arxiv.org/abs/2002.08924v1>.

*Commentary.*

A ternary nearest-neighbour local rule is a map from {0,1,2}^3 to {0,1,2}. The rule with Wolfram number N has f(a,b,c) equal to the base-3 digit of N at the position 9a + 3b + c, that is, the integer part of N divided by 3^(9a+3b+c), reduced modulo 3; the paper indexes the coefficients as a_(9x_0+3x_1+x_2) = f(x_0,x_1,x_2). Here a, b, c lie in Fin 3, the division is division of natural numbers with remainder discarded, and the result is the element of Fin 3 with that value.

**Definition 1.2 (The rule F).**

$$\operatorname{ruleF} = \operatorname{wolfram}\left(6478767664173\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.ruleF` (`✓ std3`).

*Citation.* Henryk Fukś; Roman Procyk (2019). *Explorations of Ternary Cellular Automata and Ternary Density Classification Problems*. DOI: [10.5506/APhysPolBSupp.12.75](https://doi.org/10.5506/APhysPolBSupp.12.75). URL: <https://arxiv.org/abs/2002.08924v1>.

*Commentary.*

F is the rule with Wolfram number 6478767664173; it conserves the number of each value weighted by the value, and its restriction to the values 1 and 2 is elementary rule 184.

**Definition 1.3 (The rule G).**

$$\operatorname{ruleG} = \operatorname{wolfram}\left(7580606234490\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.ruleG` (`✓ std3`).

*Citation.* Henryk Fukś; Roman Procyk (2019). *Explorations of Ternary Cellular Automata and Ternary Density Classification Problems*. DOI: [10.5506/APhysPolBSupp.12.75](https://doi.org/10.5506/APhysPolBSupp.12.75). URL: <https://arxiv.org/abs/2002.08924v1>.

*Commentary.*

G is the rule with Wolfram number 7580606234490.

**Definition 1.4 (The global map on periodic configurations).**

$$\operatorname{step}\left(f, x\right)\left(i\right) = f\left(x\left(i - 1\right), x\left(i\right), x\left(i + 1\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.step` (`✓ std3`).

*Citation.* Henryk Fukś; Roman Procyk (2019). *Explorations of Ternary Cellular Automata and Ternary Density Classification Problems*. DOI: [10.5506/APhysPolBSupp.12.75](https://doi.org/10.5506/APhysPolBSupp.12.75). URL: <https://arxiv.org/abs/2002.08924v1>.

*Commentary.*

A configuration of length L is a map x from ZMod L to Fin 3, so that indices are taken modulo L. The global map of a local rule f sends x to the configuration whose value at i is f(x(i - 1), x(i), x(i + 1)).

**Definition 1.5 (The density).**

$$\operatorname{rho}\left(x\right) = \frac{\sum_{i} x\left(i\right)}{2 \cdot L}$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.rho` (`✓ std3`).

*Citation.* Henryk Fukś; Roman Procyk (2019). *Explorations of Ternary Cellular Automata and Ternary Density Classification Problems*. DOI: [10.5506/APhysPolBSupp.12.75](https://doi.org/10.5506/APhysPolBSupp.12.75). URL: <https://arxiv.org/abs/2002.08924v1>.

*Commentary.*

For L different from 0 (NeZero L), the density of x is the rational number (1/2L) times the sum over i in ZMod L of the values x(i), read as natural numbers.

**Definition 1.6 (Conjecture 1).**

$$claim \Leftrightarrow (\forall L \in \mathbb{N}, L \neq 0 \Rightarrow \forall x \in \operatorname{ZMod}\left(L\right) \to \operatorname{Fin}\left(3\right), (\exists i, x\left(i\right) = 0) \Rightarrow \left(((\operatorname{rho}\left(x\right) \in [0, \frac{2}{3})) \Rightarrow \left(\operatorname{step}\left(\operatorname{ruleG}\right)^{[L]}\right)\left(\left(\operatorname{step}\left(\operatorname{ruleF}\right)^{[L]}\right)\left(x\right)\right) = (i \mapsto 0)) \land \left(((\operatorname{rho}\left(x\right) \in (\frac{2}{3}, \frac{3}{4})) \Rightarrow \left(\operatorname{step}\left(\operatorname{ruleG}\right)^{[L]}\right)\left(\left(\operatorname{step}\left(\operatorname{ruleF}\right)^{[L]}\right)\left(x\right)\right) = (i \mapsto 1)) \land \left((\operatorname{rho}\left(x\right) \in (\frac{3}{4}, 1)) \Rightarrow \left(\operatorname{step}\left(\operatorname{ruleG}\right)^{[L]}\right)\left(\left(\operatorname{step}\left(\operatorname{ruleF}\right)^{[L]}\right)\left(x\right)\right) = (i \mapsto 2)\right)\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.claim` (`✓ std3`).

*Citation.* Henryk Fukś; Roman Procyk (2019). *Explorations of Ternary Cellular Automata and Ternary Density Classification Problems*. DOI: [10.5506/APhysPolBSupp.12.75](https://doi.org/10.5506/APhysPolBSupp.12.75). URL: <https://arxiv.org/abs/2002.08924v1>.

*Commentary.*

Conjecture 1 of the paper: for every length L (with NeZero L) and every configuration x of length L containing at least one zero, G^L F^L(x) is the constant configuration 0 if the density lies in [0, 2/3), the constant 1 if it lies in (2/3, 3/4), and the constant 2 if it lies in (3/4, 1). In the formula the exponent [L] denotes the L-fold iterate of the global map, and (i -> c) is the constant configuration c.

**Theorem 1.7 (The configuration 210).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/fuks-2019-ternary-density-classification` (refuted) by `D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fuks-2019-ternary-density-classification","declaration_gid":"D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Henryk Fukś; Roman Procyk (2019). *Explorations of Ternary Cellular Automata and Ternary Density Classification Problems*. DOI: [10.5506/APhysPolBSupp.12.75](https://doi.org/10.5506/APhysPolBSupp.12.75). URL: <https://arxiv.org/abs/2002.08924v1>.

*Commentary.*

Take L = 3 and x = (2, 1, 0), which contains a zero and has density 3/6 = 1/2, in [0, 2/3). Decoding the Wolfram number of F gives F(0,2,1) = F(2,1,0) = F(1,0,2) = 1, so the global map of F sends x to (1, 1, 1). Both rules send (1, 1, 1) to itself, since F(1,1,1) = G(1,1,1) = 1, so G^3 F^3(x) = (1, 1, 1) and not the constant 0 that the conjecture predicts. The iterates are evaluated by decide and the density by norm_num.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.result`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.rho`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.ruleF`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.ruleG`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.step`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.wolfram`
