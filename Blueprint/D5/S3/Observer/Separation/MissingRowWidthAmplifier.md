# Missing Row Width Amplifier

## Abstract

A fixed surjective component with no surjective row admits Boolean tasks with unbounded normalized-to-original width ratios.

Let X, Y and Z be arbitrary finite nonempty sets and fix a surjection phi from X times Y onto Z. Assume that no row y maps to phi(x,y) is surjective. For each natural number m greater than the size of X let K be the cyclic group of order m, and let A and B be two separately labelled copies of the functions from Z to K. Boolean values are denoted by 0 and 1; the indicator below is Boolean valued.

$$
\begin{gathered}d = \lvert Z \rvert , S_{x} = \{\varphi(x , y) \mid y \in Y\} , r_{x} = \lvert S_{x} \rvert , r = \max_{x \in X} r_{x} \\ K = \mathbb{Z}/m \mathbb{Z} , A = K^{Z} , B = K^{Z} \\ F_{m}: A \times B \times X \times Y \to \{0 , 1\} \\ F_{m}(a , b , x , y) = \mathbf{1}_{a(\varphi(x , y)) + b(\varphi(x , y)) = 0}\end{gathered}
$$

All products associate to the right. A tuple lists coordinates with their fixed labels. The singleton set has element star. The normalized order rho is (a,b,x,y), and the original order pi is (x,a,b,y). For a fixed m, the ten maps below fix exactly the displayed prefix and leave the displayed complementary suffix free. Their dependence on the same phi and m is suppressed.

$$
\begin{gathered}\begin{gathered}L_{\rho , 0}: \{*\} \to (A \times B \times X \times Y \to \{0 , 1\}) \\ L_{\rho , 0}(*)((a , b , x , y)) = F_{m}(a , b , x , y)\end{gathered} \\ \begin{gathered}L_{\rho , 1}: A \to (B \times X \times Y \to \{0 , 1\}) \\ L_{\rho , 1}(a)((b , x , y)) = F_{m}(a , b , x , y)\end{gathered} \\ \begin{gathered}L_{\rho , 2}: A \times B \to (X \times Y \to \{0 , 1\}) \\ L_{\rho , 2}((a , b))((x , y)) = F_{m}(a , b , x , y)\end{gathered} \\ \begin{gathered}L_{\rho , 3}: A \times B \times X \to (Y \to \{0 , 1\}) \\ L_{\rho , 3}((a , b , x))(y) = F_{m}(a , b , x , y)\end{gathered} \\ \begin{gathered}L_{\rho , 4}: A \times B \times X \times Y \to (\{*\} \to \{0 , 1\}) \\ L_{\rho , 4}((a , b , x , y))(*) = F_{m}(a , b , x , y)\end{gathered}\end{gathered}
$$

$$
\begin{gathered}\begin{gathered}L_{\pi , 0}: \{*\} \to (X \times A \times B \times Y \to \{0 , 1\}) \\ L_{\pi , 0}(*)((x , a , b , y)) = F_{m}(a , b , x , y)\end{gathered} \\ \begin{gathered}L_{\pi , 1}: X \to (A \times B \times Y \to \{0 , 1\}) \\ L_{\pi , 1}(x)((a , b , y)) = F_{m}(a , b , x , y)\end{gathered} \\ \begin{gathered}L_{\pi , 2}: X \times A \to (B \times Y \to \{0 , 1\}) \\ L_{\pi , 2}((x , a))((b , y)) = F_{m}(a , b , x , y)\end{gathered} \\ \begin{gathered}L_{\pi , 3}: X \times A \times B \to (Y \to \{0 , 1\}) \\ L_{\pi , 3}((x , a , b))(y) = F_{m}(a , b , x , y)\end{gathered} \\ \begin{gathered}L_{\pi , 4}: X \times A \times B \times Y \to (\{*\} \to \{0 , 1\}) \\ L_{\pi , 4}((x , a , b , y))(*) = F_{m}(a , b , x , y)\end{gathered}\end{gathered}
$$

For each order and each index from zero through four, P and T denote the prefix and suffix products in that map's displayed type. The range is a set of actual functions on the entire labelled suffix product. Equality in a range is equality of functions on that same product. Each width is the maximum of all five range cardinalities, including the initial and terminal layers.

$$
\begin{gathered}\sigma \in \{\rho , \pi\}, i \in \{0 , 1 , 2 , 3 , 4\} \\ L_{\sigma , i}: P_{\sigma , i} \to (T_{\sigma , i} \to \{0 , 1\}) \\ \kappa_{\sigma , i}(m) = \lvert \{L_{\sigma , i}(p) \mid p \in P_{\sigma , i}\} \rvert \\ W_{\rho}(m) = \max \{\kappa_{\rho , 0}(m) , \kappa_{\rho , 1}(m) , \kappa_{\rho , 2}(m) , \kappa_{\rho , 3}(m) , \kappa_{\rho , 4}(m)\} \\ W_{\pi}(m) = \max \{\kappa_{\pi , 0}(m) , \kappa_{\pi , 1}(m) , \kappa_{\pi , 2}(m) , \kappa_{\pi , 3}(m) , \kappa_{\pi , 4}(m)\}\end{gathered}
$$

**Theorem 1.1 (Uniform missing-row amplification).**

$$\begin{gathered}\forall X, Y, Z, \operatorname{Finite}(X) \land \operatorname{Finite}(Y) \land \operatorname{Finite}(Z) \land \operatorname{Nonempty}(X) \land \operatorname{Nonempty}(Y) \land \operatorname{Nonempty}(Z) \Rightarrow \\ \forall \varphi: X \times Y \to Z, (\operatorname{Surjective}(\varphi) \land (\forall x \in X, \neg \operatorname{Surjective}((y \mapsto \varphi(x , y))))) \Rightarrow \\ (\forall x \in X, (1 \leq r_{x} \land r_{x} < d)) \\ \land r < d \\ \land (\begin{gathered}\forall m \in \mathbb{N}, \lvert X \rvert < m \Rightarrow \\ \kappa_{\rho , 0}(m) = 1 \land \kappa_{\pi , 0}(m) = 1 \\ \land \kappa_{\rho , 1}(m) = m^{d} \\ \land \kappa_{\rho , 2}(m) \leq 2^{d} \\ \land \kappa_{\rho , 3}(m) \leq \sum_{x \in X} 2^{r_{x}} \\ \land \kappa_{\rho , 4}(m) = 2 \\ \land \kappa_{\pi , 1}(m) \leq \lvert X \rvert \\ \land \kappa_{\pi , 2}(m) \leq \sum_{x \in X} m^{r_{x}} \\ \land \kappa_{\pi , 3}(m) \leq \sum_{x \in X} m^{r_{x}} \\ \land \kappa_{\pi , 4}(m) = 2 \\ \land W_{\rho}(m) = m^{d} \\ \land 0 < W_{\pi}(m) \\ \land W_{\pi}(m) \leq \sum_{x \in X} m^{r_{x}} \\ \land \sum_{x \in X} m^{r_{x}} \leq \lvert X \rvert \cdot m^{r} \\ \land \lvert X \rvert \cdot m^{r} < m^{d} \\ \land \frac{m^{d-r}}{\lvert X \rvert} \leq \frac{W_{\rho}(m)}{W_{\pi}(m)}\end{gathered}) \\ \land (\begin{gathered}\forall R \in \mathbb{R}, \exists M \in \mathbb{N}, \\ \lvert X \rvert < M \land (\forall m \in \mathbb{N}, M \leq m \Rightarrow R < \frac{W_{\rho}(m)}{W_{\pi}(m)})\end{gathered})\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/MissingRowWidthAmplifier.missing_row_width_amplifier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All displayed conclusions hold jointly. The estimates for the original intermediate layers and original width are upper bounds; they need not be attained. The quotients are real quotients of the natural state counts. In the last clause, phi, X, Y and Z stay fixed while m varies. Only the auxiliary alphabets vary, and every individual task has a finite domain and Boolean output.

Every row image is nonempty and proper. To distinguish two normalized first-layer prefixes a and a prime, choose a coordinate z where they differ, use surjectivity to write z as phi(x,y), and complete with b equal to minus a. The first response is 1 there, and the second is 0. Thus the first-layer map is injective and has m to the power d distinct responses.

After (a,b), the normalized response factors through the Boolean zero-set function on Z. After (a,b,x), it factors through a pair consisting of x and a Boolean function on its row image. In the original order, the response after (x,a) factors through x and the restriction of a to its row image; after (x,a,b), it factors through x and the restriction of a+b to that image. These factorizations retain the displayed suffix labels, including when different row images intersect. Counting the disjoint unions over x gives the stated sums as upper bounds.

The initial prefix is a singleton. At the terminal layer, the suffix is a singleton and its two Boolean functions are attained by constant sums zero and one. Since m exceeds the size of X and every row has size between one and r, all five normalized capacities are at most m to the power d, and all five original capacities are at most the displayed sum. The exponent gap d-r is positive. Given R, choose a natural N greater than R times the size of X and take M to be the maximum of N and the size of X plus one. Every m at least M then satisfies the strict ratio inequality.

## References

- Truth anchor: `D5/S3/Observer/Separation/MissingRowWidthAmplifier.missing_row_width_amplifier`
