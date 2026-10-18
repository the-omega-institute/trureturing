/* GID: D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare
   mirror-E: none(waiver:general-analytic-identity-and-tail-estimate)
   anchors: []
   utility: none
   digest: Finite prime-symbol block estimates, discrete Abel majorization and complex arithmetic tails. */

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class PrimeSymbolMeanSquareDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.";
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new System.Collections.Generic.List<Formula>
            { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }

    public DocumentDefinition Create()
    {
        Formula c = F.Id("c"), p = F.Id("p"), q = F.Id("q"), m = F.Id("m");
        Formula M = F.Id("M"), j = F.Id("j"), K = F.Id("K");
        Formula s = F.Id("s"), a = F.Id("a"), z = F.Id("z"), x = F.Id("x"), w = F.Id("w");
        Formula Dm = F.Id("D"), C = F.Id("C"), beta = F.Id("beta");
        Formula S = F.Id("S"), A = F.Id("A"), v = F.Id("v"), kappa = F.Id("kappa");
        return DocumentDefinition.Create(ScribeNode.Create(
            "SOURCE_ONLY_UNCOMPILED: author exposition; no kernel, emission or Reg acceptance claim.",
            H("Prime Symbol Mean Square"),
            Blocks(
                Paragraph(Text("All descriptions accompany the canonical-path T2 source candidate; its retained signatures, definitions and proofs preserve the pinned bytes. SOURCE_ONLY_UNCOMPILED: Lean elaboration, kernel acceptance, sorry and axiom-closure checks, scoped reports, Scribe emission, Reg, required CI and delivery remain unverified. Utility:none describes parameterized symbolic definitions, identities and estimates, including private helpers; none delivers a bounded enumeration, checker/reflection infrastructure, numerical-certificate reduction or certified fixed instance. Other utility fields are not-applicable(kind=none). No RH, Robin inequality or physical-positivity conclusion is claimed. Throughout, c,q are natural, m and block start M are integers unless a tail specifies natural M>0. Write I(c)=[2,c), a(q)=primeWeight(q)=vonMangoldt(q)/sqrt(q), L=log(c), z(c,q)=primePhase(c,q), S(c,m)=primeSymbol(c,m), D(c)=primeSquareMass(c), C(c)=primeCross(c), and B(c,M)=primeTailBudget(c,M). These display abbreviations are not new Lean declarations. The finite cutoff retains every integer and therefore every prime power. Each item also records its exact pinned signature or definition to fix all quantifiers and casts.")),
                Describe.Lean(
                    DescribeId.Create("prime-indices"),
                    DeclarationHandle.Create(Owner + "primeIndices"),
                    H("Every integer below the cutoff"),
                    StatementSource.FromAuthor(Disp(Seq(Call("I", c), Eq, Call("Ico", D(2), c)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For every natural c, I(c)=Finset.Ico 2 c. This is an interval of integers, not a set restricted to primes. Since a(q)=vonMangoldt(q)/sqrt(q), all supported higher prime powers remain in every subsequent sum; indices with zero von Mangoldt weight contribute zero.")),
                        Paragraph(Text("Exact pinned definition (source only): def primeIndices (c : ℕ) : Finset ℕ := Finset.Ico 2 c"))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("theta"),
                    DeclarationHandle.Create(Owner + "theta"),
                    H("The actual logarithmic angle"),
                    StatementSource.FromAuthor(Disp(Seq(Call("theta", c, q), Eq, Call("div", Call("log", q), Call("logLength", c))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For natural c,q, theta(c,q)=log(q)/log(c). Lean division and logarithms are total; the strict geometric assertions below require c>=2 and q in I(c). No spacing or irrationality hypothesis is added.")),
                        Paragraph(Text("Exact pinned definition (source only): def theta (c q : ℕ) : ℝ := Real.log (q : ℝ) / logLength c"))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("prime-phase"),
                    DeclarationHandle.Create(Owner + "primePhase"),
                    H("The unit-circle phase"),
                    StatementSource.FromAuthor(Disp(Seq(Call("z", c, q), Eq, Call("circleMap", D(0), D(1), Seq(D(2), Sp, F.Id("pi"), Sp, Call("theta", c, q)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For all natural c,q, z(c,q)=circleMap 0 1 (2*pi*theta(c,q)), equivalently exp(2*pi*i*theta(c,q)). Integer powers of this phase give the sine at every signed lattice mode.")),
                        Paragraph(Text("Exact pinned definition (source only): def primePhase (c q : ℕ) : ℂ := circleMap 0 1 (2 * Real.pi * theta c q)"))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("prime-symbol"),
                    DeclarationHandle.Create(Owner + "primeSymbol"),
                    H("The complete finite sine symbol"),
                    StatementSource.FromAuthor(Disp(Seq(Call("S", c, m), Eq, Call("WeightedSineSum", c, m)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For natural c and integer m, WeightedSineSum(c,m)=sum_{q in I(c)} a(q)*sin(2*pi*m*theta(c,q)). This is primeSymbol, with the positive sine sign; the owner arithmeticBoundarySymbol contains its negative. Every prime power below c is retained.")),
                        Paragraph(Text("Exact pinned definition (source only): def primeSymbol (c : ℕ) (m : ℤ) : ℝ :=   ∑ q ∈ primeIndices c, primeWeight q * Real.sin (2 * Real.pi * (m : ℝ) * theta c q)"))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("prime-square-mass"),
                    DeclarationHandle.Create(Owner + "primeSquareMass"),
                    H("The full diagonal square mass"),
                    StatementSource.FromAuthor(Disp(Seq(Call("D", c), Eq, Call("PrimeWeightSquareSum", c)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For every natural c, D(c)=sum_{q in I(c)} a(q)^2. In particular it includes squares of the weights at higher prime powers. The notation D here denotes primeSquareMass, not the generic real D in the Abel lemma.")),
                        Paragraph(Text("Exact pinned definition (source only): def primeSquareMass (c : ℕ) : ℝ := ∑ q ∈ primeIndices c, primeWeight q ^ 2"))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("ordered-cross"),
                    DeclarationHandle.Create(Owner + "orderedCross"),
                    H("Ordered unequal-pair geometric error"),
                    StatementSource.FromAuthor(Disp(Seq(Call("orderedCross", s, a, z), Eq, Call("OrderedUnequalPairSum", s, a, z)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For any finite natural set s, real a:N->R and complex z:N->C, this is sum_{p in s} sum_{q in s} (if p=q then 0 else 2*abs(a(p)*a(q))/norm(1-z(p)*conj(z(q)))). Each unordered unequal pair occurs twice, and the factor 2 is paid for each ordered pair. This definition itself assumes neither unit norms nor noncollision.")),
                        Paragraph(Text("Exact pinned definition (source only): def orderedCross (s : Finset ℕ) (a : ℕ → ℝ) (z : ℕ → ℂ) : ℝ :=   ∑ p ∈ s, ∑ q ∈ s,     if p = q then 0 else 2 * |a p * a q| / ‖1 - z p * conj (z q)‖"))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("prime-cross"),
                    DeclarationHandle.Create(Owner + "primeCross"),
                    H("The actual phase cross constant"),
                    StatementSource.FromAuthor(Disp(Seq(Call("C", c), Eq, Call("orderedCross", Call("I", c), F.Id("primeWeight"), Call("primePhase", c))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For natural c, C(c)=orderedCross(I(c),primeWeight,primePhase(c)). The actual unit phases and logarithmic noncollision theorem justify geometric denominator use when c>=2. There is no imposed spacing constant or removed prime power.")),
                        Paragraph(Text("Exact pinned definition (source only): def primeCross (c : ℕ) : ℝ := orderedCross (primeIndices c) primeWeight (primePhase c)"))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("log-length-pos"),
                    DeclarationHandle.Create(Owner + "logLength_pos"),
                    H("Positive logarithmic length"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Rightarrow, Call("Positive", Call("logLength", c))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For natural c>=2, logLength(c)=log(c)>0. This supplies the positive denominator in the actual angle comparisons.")),
                        Paragraph(Text("Exact pinned declaration signature (source only): theorem logLength_pos {c : ℕ} (hc : 2 ≤ c) : 0 < logLength c"))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("phase-geometry"),
                    DeclarationHandle.Create(Owner + "phase_geometry"),
                    H("Every included angle lies in the open unit interval"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Land, Call("Member", q, Call("I", c)), Rightarrow, Call("Positive", Call("theta", c, q)), Land, Call("LessThanOne", Call("theta", c, q))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For c>=2 and q in I(c), 0<theta(c,q)<1, since 2<=q<c and logarithm is strictly increasing on positive reals. At c=2 the membership hypothesis is empty.")),
                        Paragraph(Text("Exact pinned declaration signature (source only): theorem phase_geometry {c q : ℕ} (hc : 2 ≤ c) (hq : q ∈ primeIndices c) :     0 < theta c q ∧ theta c q < 1"))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("prime-phase-norm"),
                    DeclarationHandle.Create(Owner + "primePhase_norm"),
                    H("Unit norm without a cutoff hypothesis"),
                    StatementSource.FromAuthor(Disp(Seq(Call("norm", Call("z", c, q)), Eq, D(1)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For every natural c,q, norm(z(c,q))=1. No c>=2 or interval-membership premise is required for this circleMap identity.")),
                        Paragraph(Text("Exact pinned declaration signature (source only): theorem primePhase_norm (c q : ℕ) : ‖primePhase c q‖ = 1"))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("prime-phase-noncollision"),
                    DeclarationHandle.Create(Owner + "primePhase_noncollision"),
                    H("Difference noncollision from the actual logarithms"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Land, Call("Member", p, Call("I", c)), Land, Call("Member", q, Call("I", c)), Land, Call("Distinct", p, q), Rightarrow, Call("NotEqualOne", Seq(Call("z", c, p), Sp, Call("conj", Call("z", c, q))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For c>=2, p,q in I(c) and p!=q, z(c,p)*conj(z(c,q))!=1. The proof bounds the logarithmic difference strictly inside one period, then uses injectivity of log on positive reals. It requires no separate spacing, irrationality or equidistribution premise.")),
                        Paragraph(Text("Exact pinned declaration signature (source only): theorem primePhase_noncollision {c p q : ℕ} (hc : 2 ≤ c)     (hp : p ∈ primeIndices c) (hq : q ∈ primeIndices c) (hpq : p ≠ q) :     primePhase c p * conj (primePhase c q) ≠ 1"))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("owner-term-cutoff"),
                    DeclarationHandle.Create(Owner + "owner_term_cutoff"),
                    H("The upper-endpoint sine vanishes"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Rightarrow, Call("OwnerPrimeTerm", c, c, m), Eq, D(0)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For c>=2 and any integer m, a(c)*sin(frequency(c,m)*log(c))=0, because the angle is 2*pi*m. This permits the inclusive endpoint without deleting a nonzero contribution.")),
                        Paragraph(Text("Exact pinned declaration signature (source only): theorem owner_term_cutoff {c : ℕ} (hc : 2 ≤ c) (m : ℤ) :     primeWeight c * Real.sin (frequency c m * Real.log (c : ℝ)) = 0"))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("owner-prime-sum-eq"),
                    DeclarationHandle.Create(Owner + "owner_prime_sum_eq"),
                    H("Exact identification of the native range sum"),
                    StatementSource.FromAuthor(Disp(Seq(Call("OwnerPrimeRangeSum", c, m), Eq, Call("S", c, m)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For every natural c and integer m, sum_{q in Finset.range c} a(q)*sin(frequency(c,m)*log(q))=S(c,m). The q=0 and q=1 terms vanish; frequency(c,m)*log(q)=2*pi*m*theta(c,q). This identity has no c>=2 premise and identifies the owner prime component with its exact sign.")),
                        Paragraph(Text("Exact pinned declaration signature (source only): theorem owner_prime_sum_eq (c : ℕ) (m : ℤ) :     (∑ q ∈ Finset.range c, primeWeight q * Real.sin (frequency c m * Real.log (q : ℝ))) =       primeSymbol c m"))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("owner-prime-sum-inclusive"),
                    DeclarationHandle.Create(Owner + "owner_prime_sum_inclusive"),
                    H("The inclusive cutoff is the same symbol"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Rightarrow, Call("OwnerPrimeInclusiveSum", c, m), Eq, Call("S", c, m)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For c>=2 and any integer m, sum_{q in range(c+1)} a(q)*sin(frequency(c,m)*log(q))=S(c,m). It consumes owner_term_cutoff and owner_prime_sum_eq, with the upper term explicitly accounted for.")),
                        Paragraph(Text("Exact pinned declaration signature (source only): theorem owner_prime_sum_inclusive {c : ℕ} (hc : 2 ≤ c) (m : ℤ) :     (∑ q ∈ Finset.range (c + 1), primeWeight q * Real.sin (frequency c m * Real.log (q : ℝ))) =       primeSymbol c m"))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("prime-symbol-is-im"),
                    DeclarationHandle.Create(Owner + "primeSymbol_is_im"),
                    H("Exact complex exponential representation"),
                    StatementSource.FromAuthor(Disp(Seq(Call("S", c, m), Eq, Call("im", Call("E", c, m))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For all natural c and integer m, E(c,m)=sum_{q in I(c)} (a(q):C)*z(c,q)^m and S(c,m)=Im(E(c,m)). The exponent is an integer, so negative and zero modes are retained.")),
                        Paragraph(Text("Exact pinned declaration signature (source only): theorem primeSymbol_is_im (c : ℕ) (m : ℤ) :     primeSymbol c m =       (∑ q ∈ primeIndices c, (primeWeight q : ℂ) * primePhase c q ^ m).im"))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("geometric-block-norm"),
                    DeclarationHandle.Create(Owner + "geometric_block_norm"),
                    H("The single geometric-series estimate"),
                    StatementSource.FromAuthor(Disp(Seq(Call("UnitNorm", z), Land, Call("NotEqualOne", z), Rightarrow, Call("norm", Call("GeometricBlock", z, M, K)), Leq, Call("div", D(2), Call("norm", Seq(D(1), Minus, z)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For arbitrary complex z with norm(z)=1 and z!=1, integer M and natural K, norm(sum_{j<K} z^(M+j))<=2/norm(1-z). This includes K=0 and every signed start. It uses the existing finite geometric-sum formula, with no asymptotic averaging argument.")),
                        Paragraph(Text("Exact pinned declaration signature (source only): theorem geometric_block_norm {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1)     (M : ℤ) (K : ℕ) :     ‖∑ j ∈ Finset.range K, z ^ (M + (j : ℤ))‖ ≤ 2 / ‖1 - z‖"))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("norm-square-expansion"),
                    DeclarationHandle.Create(Owner + "norm_square_expansion"),
                    H("The full ordered complex norm-square expansion"),
                    StatementSource.FromAuthor(Disp(Seq(Call("normSq", Call("E", s, a, z, m)), Eq, Call("OrderedConjugatePairSum", s, a, z, m)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For any finite natural s, real coefficients a, arbitrary complex phases z and integer m, E(s,a,z,m)=sum_{p in s}(a(p):C)*z(p)^m. Its squared norm equals sum_{p in s}sum_{q in s} Re(((a(p)*a(q):R):C)*(z(p)*conj(z(q)))^m). Unit norm and noncollision are not hypotheses of this algebraic identity; the ordered complex summands are not assumed symmetric.")),
                        Paragraph(Text("Exact pinned declaration signature (source only): theorem norm_square_expansion (s : Finset ℕ) (a : ℕ → ℝ) (z : ℕ → ℂ) (m : ℤ) :     ‖∑ p ∈ s, (a p : ℂ) * z p ^ m‖ ^ 2 =       ∑ p ∈ s, ∑ q ∈ s, (((a p * a q : ℝ) : ℂ) * (z p * conj (z q)) ^ m).re"))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("prime-symbol-block"),
                    DeclarationHandle.Create(Owner + "prime_symbol_block"),
                    H("Uniform finite blocks with every prime power"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Rightarrow, Call("SquareBlock", c, M, K), Leq, Sp, Seq(K, Sp, Call("D", c), Plus, Call("C", c))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For c>=2, any integer M and any natural K, SquareBlock(c,M,K)=sum_{j<K} S(c,M+j)^2 <= K*D(c)+C(c). The proof bounds the imaginary square by the complex norm square and applies geometric_block_norm to ordered unequal pairs. K=0 and negative block starts are admitted.")),
                        Paragraph(Text("Exact pinned declaration signature (source only): theorem prime_symbol_block {c : ℕ} (hc : 2 ≤ c) (M : ℤ) (K : ℕ) :     (∑ j ∈ Finset.range K, primeSymbol c (M + (j : ℤ)) ^ 2) ≤       (K : ℝ) * primeSquareMass c + primeCross c"))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("finite-abel-majorant"),
                    DeclarationHandle.Create(Owner + "finite_abel_majorant"),
                    H("Discrete Abel majorization with exact hypotheses"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AbelHypotheses", x, w, Dm, C), Rightarrow, Call("WeightedPartialSum", x, w, K), Leq, Sp, Seq(Dm, Sp, Call("WeightPartialSum", w, K), Plus, C, Sp, Call("AtZero", w))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For x,w:N->R and D,C:R, assume 0<=C, every w(i)>=0, w(i+1)<=w(i), and for every natural k, sum_{i<k}x(i)<=k*D+C. Then for every natural K, sum_{i<K}x(i)*w(i)<=D*sum_{i<K}w(i)+C*w(0). No sign hypothesis is imposed on x or D. The proof uses Mathlib finite summation by parts and retains its finite boundary contribution, including K=0.")),
                        Paragraph(Text("Exact pinned declaration signature (source only): theorem finite_abel_majorant (x w : ℕ → ℝ) (D C : ℝ)     (hC : 0 ≤ C) (hw : ∀ i, 0 ≤ w i) (hanti : ∀ i, w (i + 1) ≤ w i)     (hA : ∀ K, (∑ i ∈ Finset.range K, x i) ≤ (K : ℝ) * D + C) (K : ℕ) :     (∑ i ∈ Finset.range K, x i * w i) ≤       D * (∑ i ∈ Finset.range K, w i) + C * w 0"))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("inverse-square-weight"),
                    DeclarationHandle.Create(Owner + "inverseSquareWeight"),
                    H("The actual positive-tail enumeration weight"),
                    StatementSource.FromAuthor(Disp(Seq(Call("W", M, j), Eq, Call("square", Call("inv", Seq(M, Plus, j, Plus, D(1))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For natural M,j, W(M,j)=((M:R)+(j:R)+1)^(-2), written in Lean as the square of the inverse. The enumeration m=M+j+1 visits each positive mode above M exactly once.")),
                        Paragraph(Text("Exact pinned definition (source only): def inverseSquareWeight (M j : ℕ) : ℝ := (((M : ℝ) + (j : ℝ) + 1)⁻¹) ^ 2"))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("prime-tail-budget"),
                    DeclarationHandle.Create(Owner + "primeTailBudget"),
                    H("The unrefined prime tail budget"),
                    StatementSource.FromAuthor(Disp(Seq(Call("B", c, M), Eq, Call("div", Call("D", c), M), Plus, Call("div", Call("C", c), Call("square", Seq(M, Plus, D(1))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For natural c,M, B(c,M)=D(c)/M+C(c)/(M+1)^2. This is primeTailBudget; the convergent-tail estimates below require c>=2 and M>0. The first term uses the inverse-square partial-sum bound 1/M.")),
                        Paragraph(Text("Exact pinned definition (source only): def primeTailBudget (c M : ℕ) : ℝ :=   primeSquareMass c / (M : ℝ) + primeCross c / ((M : ℝ) + 1) ^ 2"))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("inverse-square-weight-antitone"),
                    DeclarationHandle.Create(Owner + "inverseSquareWeight_antitone"),
                    H("Antitonicity of the sampled inverse square"),
                    StatementSource.FromAuthor(Disp(Seq(Call("Positive", M), Rightarrow, Call("W", M, Seq(j, Plus, D(1))), Leq, Call("W", M, j)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For natural M>0 and every natural j, inverseSquareWeight(M,j+1)<=inverseSquareWeight(M,j). This is the exact weight monotonicity supplied to finite_abel_majorant.")),
                        Paragraph(Text("Exact pinned declaration signature (source only): theorem inverseSquareWeight_antitone {M : ℕ} (hM : 0 < M) (i : ℕ) :     inverseSquareWeight M (i + 1) ≤ inverseSquareWeight M i"))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("prime-symbol-square-tail"),
                    DeclarationHandle.Create(Owner + "prime_symbol_square_tail"),
                    H("Summability before the actual prime-square tsum bound"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Land, Call("Positive", M), Rightarrow, Call("Summable", Call("PrimeEnergySequence", c, M)), Land, Call("PrimeEnergyTsum", c, M), Leq, Call("B", c, M)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For c>=2 and M>0, the nonnegative sequence j |-> S(c,M+j+1)^2*W(M,j) is summable, and its actual tsum is <=B(c,M). Uniformly bounded partial sums establish summability first; a totalized divergent tsum is not used. Every m>M is present.")),
                        Paragraph(Text("Exact pinned declaration signature (source only): theorem prime_symbol_square_tail {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M) :     Summable (fun j : ℕ =>       primeSymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight M j) ∧     (∑' j : ℕ, primeSymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight M j) ≤       primeTailBudget c M"))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("complex-prime-energy"),
                    DeclarationHandle.Create(Owner + "complex_prime_energy"),
                    H("Exact complex scaling of the energy"),
                    StatementSource.FromAuthor(Disp(Seq(Call("ComplexEnergy", c, M, j, beta), Eq, Call("normSq", beta), Sp, Call("square", Call("S", c, Seq(M, Plus, j, Plus, D(1)))), Sp, Call("W", M, j)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For all natural c,M,j and arbitrary complex beta, norm(beta*(S(c,M+j+1):C)/(M+j+1:C))^2=norm(beta)^2*(S(c,M+j+1)^2*W(M,j)). There are no c>=2, M>0, reality or cancellation premises for this exact identity.")),
                        Paragraph(Text("Exact pinned declaration signature (source only): theorem complex_prime_energy (c M j : ℕ) (β : ℂ) :     ‖β * (primeSymbol c ((M + j + 1 : ℕ) : ℤ) : ℂ) / ((M + j + 1 : ℕ) : ℂ)‖ ^ 2 =       ‖β‖ ^ 2 * (primeSymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight M j)"))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("complex-prime-tail"),
                    DeclarationHandle.Create(Owner + "complex_prime_tail"),
                    H("An actual tail for arbitrary complex beta"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Land, Call("Positive", M), Rightarrow, Call("Summable", Call("ComplexPrimeEnergySequence", c, M, beta)), Land, Call("ComplexPrimeEnergyTsum", c, M, beta), Leq, Call("normSq", beta), Sp, Call("B", c, M)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For c>=2, M>0 and any beta:C, j |-> norm(beta*S(c,M+j+1)/(M+j+1))^2 is summable and its tsum is <=norm(beta)^2*(D(c)/M+C(c)/(M+1)^2). The coefficient remains arbitrary complex and its exact squared norm is retained.")),
                        Paragraph(Text("Exact pinned declaration signature (source only): theorem complex_prime_tail {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M) (β : ℂ) :     Summable (fun j : ℕ =>       ‖β * (primeSymbol c ((M + j + 1 : ℕ) : ℤ) : ℂ) / ((M + j + 1 : ℕ) : ℂ)‖ ^ 2) ∧     (∑' j : ℕ,       ‖β * (primeSymbol c ((M + j + 1 : ℕ) : ℤ) : ℂ) / ((M + j + 1 : ℕ) : ℂ)‖ ^ 2) ≤         ‖β‖ ^ 2 * (primeSquareMass c / (M : ℝ) + primeCross c / ((M : ℝ) + 1) ^ 2)"))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("retained-boundary-moment"),
                    DeclarationHandle.Create(Owner + "retainedBoundaryMoment"),
                    H("The complete retained complex boundary moment"),
                    StatementSource.FromAuthor(Disp(Seq(Call("Moment", c, S, A, v, j), Eq, Call("WeightedBoundaryMomentSum", c, S, A, v, j)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For natural c,j, finite S subset N, A:N->R and v:N->C, Moment(c,S,A,v,j)=sum_{n in S}(-1)^n*(A(n):C)*v(n)*(frequency(c,(n:Z)):C)^(2*j). The amplitudes, phases, arbitrary complex coefficients and owner frequency are all retained.")),
                        Paragraph(Text("Exact pinned definition (source only): def retainedBoundaryMoment (c : ℕ) (S : Finset ℕ) (A : ℕ → ℝ)     (v : ℕ → ℂ) (j : ℕ) : ℂ :=   ∑ n ∈ S, (-1 : ℂ) ^ n * (A n : ℂ) * v n *     (frequency c (n : ℤ) : ℂ) ^ (2 * j)"))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("retained-arithmetic-column"),
                    DeclarationHandle.Create(Owner + "retainedArithmeticColumn"),
                    H("The finite sum of actual prime-symbol columns"),
                    StatementSource.FromAuthor(Disp(Seq(Call("RetainedColumn", c, S, A, v, j, kappa, m), Eq, Call("PrimeColumnSum", c, S, A, v, j, kappa, m)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For natural c,j,m, finite S subset N, real A, complex v and arbitrary kappa:C, the column is sum_{n in S} kappa*((-1)^n*(A(n):C)*v(n)*(frequency(c,n):C)^(2*j))*(S(c,m):C)/(m:C). Here S(c,m) denotes the prime sine symbol, while the set S is the finite index set. Kappa is explicit normalization supplied by the caller.")),
                        Paragraph(Text("Exact pinned definition (source only): def retainedArithmeticColumn (c : ℕ) (S : Finset ℕ) (A : ℕ → ℝ)     (v : ℕ → ℂ) (j : ℕ) (κ : ℂ) (m : ℕ) : ℂ :=   ∑ n ∈ S, κ * ((-1 : ℂ) ^ n * (A n : ℂ) * v n *     (frequency c (n : ℤ) : ℂ) ^ (2 * j)) * (primeSymbol c (m : ℤ) : ℂ) / (m : ℂ)"))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("retained-arithmetic-tail"),
                    DeclarationHandle.Create(Owner + "retained_arithmetic_tail"),
                    H("The retained moment controls its genuine infinite tail"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Land, Call("Positive", M), Rightarrow, Call("Summable", Call("RetainedColumnEnergySequence", c, M, S, A, v, j, kappa)), Land, Call("RetainedColumnEnergyTsum", c, M, S, A, v, j, kappa), Leq, Call("normSq", kappa), Sp, Call("normSq", Call("Moment", c, S, A, v, j)), Sp, Call("B", c, M)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For c>=2, M>0 and every finite S subset N, A:N->R, v:N->C, natural j and kappa:C, the column energy at m=M+k+1 is summable in k. Its tsum is <=norm(kappa)^2*norm(Moment(c,S,A,v,j))^2*B(c,M). The finite sum is collected algebraically before applying complex_prime_tail. No moment is set to zero and no reality assumption is imposed on v or kappa.")),
                        Paragraph(Text("Exact pinned declaration signature (source only): theorem retained_arithmetic_tail {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M)     (S : Finset ℕ) (A : ℕ → ℝ) (v : ℕ → ℂ) (j : ℕ) (κ : ℂ) :     Summable (fun k : ℕ => ‖retainedArithmeticColumn c S A v j κ (M + k + 1)‖ ^ 2) ∧     (∑' k : ℕ, ‖retainedArithmeticColumn c S A v j κ (M + k + 1)‖ ^ 2) ≤       ‖κ‖ ^ 2 * ‖retainedBoundaryMoment c S A v j‖ ^ 2 *         (primeSquareMass c / (M : ℝ) + primeCross c / ((M : ℝ) + 1) ^ 2)"))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("canonical-prime-first-jet-far"),
                    DeclarationHandle.Create(Owner + "canonicalPrimeFirstJetFar"),
                    H("The canonical positive-sign prime far term"),
                    StatementSource.FromAuthor(Disp(Seq(Call("PrimeFar", c, S, v, m), Eq, Call("div", Seq(Call("S", c, m), Sp, Call("CoefficientSum", S, v)), Seq(F.Id("pi"), Sp, m))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For natural c, finite S subset Z, v:Z->C and any integer m, PrimeFar(c,S,v,m)=(primeSymbol(c,m):C)*sum_{n in S}v(n)/((pi:C)*(m:C)). The positive sign follows from subtracting the exterior arithmetic symbol, whose prime component is negative. The exact pi normalization is preserved.")),
                        Paragraph(Text("Exact pinned definition (source only): def canonicalPrimeFirstJetFar (c : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (m : ℤ) : ℂ :=   (primeSymbol c m : ℂ) * (∑ n ∈ S, v n) / ((Real.pi : ℂ) * (m : ℂ))"))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("canonical-first-jet-split"),
                    DeclarationHandle.Create(Owner + "canonical_first_jet_split"),
                    H("An exact split of the existing first jet"),
                    StatementSource.FromAuthor(Disp(Seq(Call("couplingFirstJet", c, S, v, m), Eq, Call("div", Call("InteriorSymbolMoment", c, S, v), Seq(F.Id("pi"), Sp, m)), Minus, Call("div", Seq(Grp(Call("arithmeticBoundarySymbol", c, m), Plus, Call("S", c, m)), Sp, Call("CoefficientSum", S, v)), Seq(F.Id("pi"), Sp, m)), Plus, Call("PrimeFar", c, S, v, m)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For every natural c, finite integer S, arbitrary complex v and integer m, Jet(c,S,v,m)=alpha/(pi*m)-(arithmeticBoundarySymbol(c,m)+primeSymbol(c,m))*beta/(pi*m)+PrimeFar(c,S,v,m), where alpha=sum_{n in S}(arithmeticBoundarySymbol(c,n):C)*v(n) and beta=sum_{n in S}v(n). All real symbols are cast to C. This is an exact totalized-division identity, with no exterior or nonzero-mode hypothesis. The interior full symbol and exterior nonprime component remain present; it does not assert the separate full-symbol physical bridge.")),
                        Paragraph(Text("Exact pinned declaration signature (source only): theorem canonical_first_jet_split (c : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (m : ℤ) :     couplingFirstJet c S v m =       (∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n) /         ((Real.pi : ℂ) * (m : ℂ)) -       ((arithmeticBoundarySymbol c m + primeSymbol c m : ℝ) : ℂ) *         (∑ n ∈ S, v n) / ((Real.pi : ℂ) * (m : ℂ)) +       canonicalPrimeFirstJetFar c S v m"))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("canonical-first-jet-prime-tail"),
                    DeclarationHandle.Create(Owner + "canonical_first_jet_prime_tail"),
                    H("The exact pi-normalized first-jet prime tail"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Land, Call("Positive", M), Rightarrow, Call("Summable", Call("PrimeFarEnergySequence", c, M, S, v)), Land, Call("PrimeFarEnergyTsum", c, M, S, v), Leq, Call("div", Call("normSq", Call("CoefficientSum", S, v)), Call("square", F.Id("pi"))), Sp, Call("B", c, M)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For c>=2, M>0, every finite S subset Z and arbitrary complex v, j |-> norm(PrimeFar(c,S,v,M+j+1))^2 is summable. Its tsum is <=(norm(sum_{n in S}v(n))^2/pi^2)*(D(c)/M+C(c)/(M+1)^2). This is the actual existing first-jet prime term with its pi^(-2) factor; the nonprime component and column remainder remain separate.")),
                        Paragraph(Text("Exact pinned declaration signature (source only): theorem canonical_first_jet_prime_tail {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M)     (S : Finset ℤ) (v : ℤ → ℂ) :     Summable (fun k : ℕ => ‖canonicalPrimeFirstJetFar c S v ((M + k + 1 : ℕ) : ℤ)‖ ^ 2) ∧     (∑' k : ℕ, ‖canonicalPrimeFirstJetFar c S v ((M + k + 1 : ℕ) : ℤ)‖ ^ 2) ≤       (‖∑ n ∈ S, v n‖ ^ 2 / Real.pi ^ 2) *         (primeSquareMass c / (M : ℝ) + primeCross c / ((M : ℝ) + 1) ^ 2)"))),
                    DescribeRole.Theorem))));
    }
}
