# Golden Cubic Compatibility Density

## Abstract

Actual cubic compatibility and full-support golden-clock comparison primes.

**Theorem 1.1 (Exact unrestricted rational-prime density).**

Lean statement: `D5/S3/Factorization/Galois/GoldenCubicCompatibilityDensity.actual_compatibility_density`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/GoldenCubicCompatibilityDensity.actual_compatibility_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each unit residue a modulo 80 times 3 to the power j plus 2 with image one modulo three, unrestricted rational primes in that class whose prime above E has the actual character-defined Frobenius have Dirichlet density two divided by the totient of the modulus and 3 to the power twice the earlier support size plus two. This density is positive.

The proof applies the cited general Chebotarev theorem to the computed two-element class, removes finite modulus and ramification exceptions, and identifies the prime-ideal Dirichlet series with the rational-prime series. Separately, there exists a unit residue b with positive representative that reduces to one modulo three and satisfies the oddness, quadratic-character and stated congruence conditions. Positive density among unrestricted primes does not assert a prime in the finite current block.

## Original GPC7: full-support golden-clock comparison primes

Fix j >= 2. Write L_n = goldenLucas(n), B_i = |L_(3^i)^2 + 3|, S = union_{1 <= i < j} primeFactors(B_i), t = |S|, r = 3^(j+1), M = 40r, A = product_{p in S} p and N = MA. Every distinct earlier prime belongs to S, including primes occurring with even initial depth. The comparison set C consists of rational primes Q with Q = 19 modulo 40, Q = 1 modulo r, and Jacobi(p,Q) = 1 for every p in S. There is no condition on division of B_j, the exact Pisano period or the initial Wall-Sun-Sun depth in this definition.

The congruences in D5.S1.Scale.golden_cubic_lucas_block give B_i = 1 modulo 9 and B_i = 19 modulo 80. Thus no support prime is 2, 3 or 5, so the distinct moduli p in S are pairwise coprime and all are coprime to M. The two fixed congruences specify one unit class modulo M. If Q belongs to C, they imply gcd(Q,M)=1; also Q cannot equal any p in S, since Jacobi(p,p)=0. Consequently gcd(Q,N)=1 follows from the literal definition of C. It is a consequence used in the argument, with no extra restriction on C.

## Independent signs and the literal residue union

For each p in S choose a sign eta_p in {1,-1}. In the unit group modulo the odd prime p, the quadratic character is nontrivial and takes values in {1,-1}. Multiplication by a unit of character -1 bijects its two fibers. They partition the p-1 units, so either prescribed sign has (p-1)/2 solutions. CRT between 40, r and every p in S therefore gives exactly product_{p in S} ((p-1)/2) unit classes modulo N having the two fixed residues and any prescribed vector of signs. This includes the empty-support convention, with empty product one.

For the original splitting tests take eta_p = (-1)^((p-1)/2). Every prime in the fixed class is 3 modulo 4. Quadratic reciprocity, with Q distinct from p, says Jacobi(p,Q)=1 if and only if Jacobi(Q,p)=eta_p. Let R be exactly the finite set of unit classes modulo N with these signs and the two fixed residues. A prime in C is coprime to N by the preceding argument, hence defines a unit in R. Conversely a prime reducing to R satisfies the fixed congruences and reciprocity gives every Jacobi(p,Q)=1. Thus C equals the union of the residue classes in R, in both directions and without deleting any primes.

## Actual cyclotomic Frobenius and Dirichlet density

Use the actual field K = Q(zeta_N) and the cyclotomic isomorphism e = IsCyclotomicExtension.Rat.galEquivZMod from Gal(K/Q) to the units modulo N. For a rational prime Q coprime to N, the ideal q=(Q) in the ring of integers of Q has absolute norm Q and is unramified in K. At any prime P of K above q, arithmetic Frobenius sends zeta_N to zeta_N^Q. This is the primitive-root power argument already used inside the tracked owner D5/S3/Analytic/Zeta/NumberField/ZetaProductFibre.lean. Applying the cyclotomic isomorphism therefore gives e(Frob_P)=the unit represented by Q.

This also identifies the actual conjugacy class. For any actual automorphisms x,y, a conjugacy relation between x and y maps under e to conjugacy of units. The unit group is commutative, so e(x)=e(y), and injectivity gives x=y in the original automorphism group. Consequently the actual Frobenius class is the class of e^(-1)(a) exactly when Q reduces to the unit a. The reverse direction applies the class map to that equality. The comparison uses the actual field automorphisms and their conjugacy relation throughout.

Chebotarev.chebotarev_abelian applied to K/Q gives density 1/phi(N) for each such singleton class. The equivalent cyclotomic formula is Chebotarev.cyclotomic_density_from_two_sided_asymp; its conductor condition N modulo 4 != 2 holds since 40 divides N. The bijection Q -> (Q) between rational primes and nonzero prime ideals of the integers of Q preserves absolute norm. Thus it identifies the corresponding Dirichlet series term by term. The finitely many conductor-divisor exceptions have zero Dirichlet density. Finite disjoint addition over R gives density |R|/phi(N) for the literal C.

Here Dirichlet density has exactly the normalization HasRationalPrimeDirichletDensity in the existing density owner: the limit, as real s decreases to 1 through s>1, of (sum_{Q in C} Q^(-s))/(sum_{Q rational prime} Q^(-s)). Since A is squarefree and coprime to M, phi(N)=phi(M) product_{p in S}(p-1). Substituting the CRT count gives |R|/phi(N)=1/(2^t phi(M)). Multiplicativity and the prime-power totient formula give phi(40*3^(j+1))=16*(2*3^j)=32*3^j. The density is therefore exactly 1/(2^(t+5)*3^j)>0. This conclusion concerns the displayed Dirichlet-series limit; no natural prime-counting density conclusion is used.

## The exact golden clock and its converse

Let pi(Q) be the Pisano period and let phi be the golden generator with phi^2=phi+1. The injective multiplication-matrix representation goldenMatrixHom sends phi to the Fibonacci matrix [[1,1],[1,0]], so it preserves its order. The public theorem D5.S3.Arith.PisanoMatrixBridge.pisanoPeriod_eq_matrix_order identifies that matrix order with pi(Q) for Q>1.

Suppose Q>5 is prime and pi(Q)=2r. Then w=phi^(2*3^j) in GoldenMod(Q) has exact order three and norm one. If bar(w) denotes golden conjugation, norm one gives w*bar(w)=1, while w^3=1 gives w^2=bar(w). Hence w^2+w+1 is the scalar trace(w)+1. Multiplying by w-1 gives zero. Write w=a+b*phi and tau=2a+b+1. The two coordinates of this scalar product say tau*(a-1)=0 and tau*b=0 in the field ZMod(Q). If tau were nonzero, they would force a=1 and b=0, contrary to w having order three. Thus trace(w)=-1. This coordinate argument applies to the golden algebra in both the split and inert cases.

The trace identity D5.S1.Scale.golden_lucas_two_mul, with the odd index n=3^j, gives trace(phi^(2n))+1=L_n^2+3. Therefore Q divides B_j. Conversely, D5.S3.Arith.Primes.GoldenCubicBlockPrimePeriods.cubic_block_b_prime_period gives matrix order 2*3^(j+1) for every prime divisor of B_j, and the Pisano matrix bridge gives pi(Q)=2r. Thus, for every prime Q>5, pi(Q)=2r if and only if Q divides B_j. The congruences above exclude 2,3,5 from this support. Since B_j is a positive nonzero integer, these exact-clock primes form precisely its finite prime-factor set.

## The actual cubic compatibility field uses the same support

The existing cubic construction can be read with the same B_i and S. Its blockValue(i) is blockNorm((L_(3^i)-1).toNat); for i>=1 the Lucas value is positive, and the Eisenstein norm (L-1)^2+2(L-1)+4=L^2+3 identifies this with B_i. Its support(j) is the same union over 1<=i<j. Its modulus m=80*3^(j+2) equals 6M. Keep this modulus and the cubic prime event explicit when applying actual_compatibility_density.

Work inside the actual algebraic closure of E=Q(zeta_3). Choose the primary Eisenstein prime pi_p of norm p for each p in S, as supplied by actual_complete_cubic_cyclotomic_disjointness in GoldenCubicCompleteCyclotomicDisjointness. The radical indices are (S x Bool) disjoint-union Fin(2): adjoining the cube roots of pi_p and its conjugate for every p, together with cube roots of 2 and 3, gives the actual radical field M_3. It has degree 3^(2t+2) over E and Galois group with one independent ZMod(3) coordinate per radical index. For a primitive m-th root zeta, put C_3=E(zeta) and F_3=M_3 C_3. The supplied disjointness is M_3 intersect C_3=E, so restriction identifies Gal(F_3/E) with Gal(M_3/E) x Gal(C_3/E).

Write omega for the Eisenstein cube root of unity, xi for its image in E, lambda=1+2omega, and kappa_p for the image of the local cubic symbol (lambda/(pi_p)). The selected radical automorphism g_M multiplies the cube root of pi_p by kappa_p^2, the cube root of its conjugate by kappa_p^(-2), and each of the cube roots of 2 and 3 by xi^2. These are the actual character coordinates, with the primes, roots and primary choices supplied together. Given a unit a modulo m reducing to one modulo three, the cyclotomic automorphism sigma_a:zeta -> zeta^a fixes E. The restriction-product equivalence combines g_M and sigma_a into g_F; viewing this as a rational automorphism gives g_Q. This is the parameter correspondence in actual_compositum_data, rather than an independent choice of a synthetic finite group.

The theorem actual_conjugacy_data, with the compositum data supplied by actual_compositum_data, identifies the rational conjugacy class as {g_Q,theta}, where theta is its conjugate by complex conjugation. They differ on the real cube root of 2: their multipliers are xi^2 and xi. Automorphisms fixing E form an abelian subgroup of index two, so these are all rational conjugates. The class has size two and |Gal(F_3/Q)|=phi(m)*3^(2t+2).

For these same choices define T_a to be the rational primes Q with Q=a modulo m and with a prime q_E of E above Q and a prime q_M of M_3 above q_E at which g_M is arithmetic Frobenius. The existential primes, the actual fields and the specified automorphism are part of this event. Since a reduces to one modulo three, such Q splits in E and its residue degree there is one. Away from ramification, choose a prime of F_3 above q_M. Frobenius restricts to g_M on M_3 and to sigma_a on C_3, the latter by the cyclotomic residue calculation and Norm(q_E)=Q. The product equivalence forces it to be g_F, giving the rational class of g_Q. Conversely, if the rational Frobenius class is that of g_Q, the actual Frobenius at an upper prime is either g_Q or theta. In the second case complex conjugation transports the upper prime to one with Frobenius g_Q. Restriction then supplies the required q_E and q_M with Frobenius g_M, while restriction to C_3 recovers Q=a modulo m. Thus away from ramification and the conductor these events are equivalent in both directions, for the same actual fields and roots. This is the field-and-class transfer used by the tracked proof of actual_compatibility_density.

That public theorem proves that the unrestricted set T_a has positive Dirichlet density 2/(phi(m)*3^(2t+2)). Its proof applies the general Chebotarev theorem to the two-element class, removes the finite ramified and conductor-divisor sets, and uses Q -> (Q) and the norm equality to transfer the ideal series to rational primes. The cubic formula is for T_a; the quadratic formula 1/(2^t phi(M)) is for the literal set C. In particular, using the actual cubic construction preserves its residue and Frobenius conditions and does not identify these two prime sets or impose division of the current block.

## Applicability and the remaining arithmetic conditions

The positive Dirichlet density for C establishes compatibility of the finite earlier-prime quadratic tests among unrestricted comparison primes. At fixed j the exact-clock set is finite, so the density gives no prime with the additional condition pi(Q)=2r or Q dividing B_j. Neither density result supplies an initial Wall-Sun-Sun depth at least two or an all-Wall-Sun-Sun realization of B_j=P^2 Q^3. The latter realization and its impossibility remain open alternatives.

These arguments are applications of the cited existing results. The original Wall-Sun-Sun existence and infinitude questions remain open; PH remains an independent hypothesis where used, and the powerful Fibonacci classification remains open. Results assuming an existing golden packet retain that premise and do not construct a new packet or a new element of X_(p,k). The established union infinitude does not select between infinitely many depth-one primes and infinitely many primes of odd depth at least three. The quadratic reciprocity constraints record parity of the actual depths and leave these arithmetic realization questions intact.

## References

- Truth anchor: `D5/S3/Factorization/Galois/GoldenCubicCompatibilityDensity.actual_compatibility_density`
- Dependency: [D5/S3/Factorization/Galois/GoldenCubicCompatibilityPrimeTransfer](GoldenCubicCompatibilityPrimeTransfer.md)
