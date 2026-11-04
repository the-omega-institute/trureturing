using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class FractionalSchattenAlignmentRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Eigenstructure/alhejjiknill2024spinalignment");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Domination of every word trace does not order Schatten norms of non-integer order.",
        H("Word traces do not control fractional Schatten norms"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fractional-schatten-alignment-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The proposed implication for every real order at least one"),
                StatementSource.FromAuthor(Disp(Equal(Typed(Local("claim"), Qualified("Prop")),
                    Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Alhejji and Knill ask whether domination of the traces of all ordered products "
                            + "of two positive semidefinite matrices, with the individual spectra fixed, "
                            + "implies domination of the Schatten norms of their sums for every real p ≥ 1 "
                            + "(arXiv:2307.06894v3, main.tex, line 759). Their spectrum lists eigenvalues "
                            + "with multiplicity (line 117), and their Schatten norm is "
                            + "‖R‖ₚ = (tr |R|ᵖ)^(1/p), with |R| = √(RᴴR), where Rᴴ is the adjoint "
                            + "(lines 274–278).")),
                    Paragraph(Text(
                        "The assertion quantifies over every natural matrix size m, including zero, "
                            + "and four complex matrices a₀, a₁, b₀, b₁ of that size. Each matrix is "
                            + "positive semidefinite, and the characteristic polynomials agree for a₀ "
                            + "and b₀ and for a₁ and b₁. For these Hermitian matrices, the latter equalities "
                            + "express equality of spectra with multiplicity. A Boolean word s selects "
                            + "the subscript one at true and zero at false; its ordered product is taken "
                            + "from left to right, and the empty product is the identity. For every word, "
                            + "the a-trace has imaginary part zero and its real part is at least the "
                            + "complex norm of the b-trace. The conclusion compares the Schatten norms "
                            + "of b₀ + b₁ and a₀ + a₁ at every real p ≥ 1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fractional-schatten-alignment-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A diagonal counterexample at order three halves"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take A₀ = B₀ = diag(0, 1, 1, 2), A₁ = diag(1, 0, 1, 2), "
                            + "and B₁ = diag(0, 1, 2, 1), as complex matrices of size four. "
                            + "For diagonal matrices with diagonals d₀ and d₁, induction on a Boolean "
                            + "word s shows that its ordered product is diagonal with kth entry "
                            + "d₀(k)^m d₁(k)^n, where m counts false and n counts true. "
                            + "The empty word gives the identity, and adjoining either letter multiplies "
                            + "the corresponding diagonal entry and increments its count.")),
                    Paragraph(Text(
                        "Taking traces gives tr Πs(A₀,A₁) = ↑(0^m + 0^n + 1 + 2^(m+n)) "
                            + "and tr Πs(B₀,B₁) = ↑(0^(m+n) + 1 + 2^m + 2^n), "
                            + "where each expression inside ↑ is a natural number, included in ℂ, "
                            + "and 0^0 = 1. If either count is zero the two natural numbers agree. "
                            + "If both counts are positive, 2 ≤ 2^m and 2 ≤ 2^n imply "
                            + "2^m + 2^n ≤ 2^m · 2^n = 2^(m+n); adding one gives the required "
                            + "comparison because all three relevant positive powers of zero vanish.")),
                    Paragraph(Text(
                        "All diagonal entries are nonnegative, so the four matrices are positive "
                            + "semidefinite. The equality A₀ = B₀ gives one characteristic-polynomial "
                            + "equality. Expanding the diagonal characteristic polynomials for A₁ and B₁ "
                            + "gives the same product of the four linear factors in a different order, "
                            + "so the other equality also holds. The trace formulas are complex inclusions "
                            + "of natural numbers, hence have imaginary part zero; the norm and real part "
                            + "of each inclusion are that natural number cast to ℝ. The natural-number "
                            + "comparison therefore proves the required word-trace inequalities.")),
                    Paragraph(Text(
                        "For a real nonnegative diagonal d and a real p ≥ 1, the Schatten norm of "
                            + "diag(k ↦ (d(k) : ℂ)) is (Σk d(k)^p)^(1/p). To obtain this identity, "
                            + "write D = diag(k ↦ (d(k) : ℂ)). Then Dᴴ · (Dᴴ)ᴴ = DᴴD is "
                            + "diag(k ↦ ((d(k)^2 : ℝ) : ℂ)). Continuous functional calculus acts "
                            + "entry by entry on this diagonal matrix. Taking the trace and then its "
                            + "real part reduces the expression to a sum, and nonnegativity gives "
                            + "(d(k)^2)^(p/2) = d(k)^p.")),
                    Paragraph(Text(
                        "The sums A₀ + A₁ and B₀ + B₁ have diagonals (1, 1, 2, 4) and "
                            + "(0, 2, 3, 3), respectively. Their entries are nonnegative. At p = 3/2, "
                            + "the diagonal norm identity and strict monotonicity of the real power "
                            + "x ↦ x^(2/3) on nonnegative x reduce the strict norm comparison to "
                            + "1^(3/2) + 1^(3/2) + 2^(3/2) + 4^(3/2) "
                            + "< 0^(3/2) + 2^(3/2) + 3^(3/2) + 3^(3/2). "
                            + "Here 4^(3/2) = 8 and 3^(3/2) = 3√3. After cancellation the inequality "
                            + "is 10 < 6√3, which follows from (√3)^2 = 3 and √3 ≥ 0 "
                            + "since 100 < 108. Thus ‖A₀ + A₁‖₃⁄₂ < ‖B₀ + B₁‖₃⁄₂.")),
                    Paragraph(Text(
                        "If the asserted implication held, its instance at size four, these matrices "
                            + "and p = 3/2 would give the opposite weak inequality. The strict comparison "
                            + "contradicts it. This disproves the implication from all word traces to "
                            + "all real orders p ≥ 1; it does not decide the spin alignment conjecture itself.")),
                    Paragraph(Text(
                        "A stronger application uses one common diagonal quadruple on each entire interval (k, k+1), for every integer k ≥ 1. For k = 1, add the identity to each of the four displayed matrices: A₀ = B₀ = diag(1, 2, 2, 3), A₁ = diag(2, 1, 2, 3), and B₁ = diag(1, 2, 3, 2). Their sums have the respective diagonal lists (3, 3, 4, 6) and (2, 4, 5, 5). The common trace of the four individual matrices is eight. These are the shifted source matrices on their actual shared coordinates.")),
                    Paragraph(Text(
                        "For k ≥ 2, put r = k + 2, q = k + 1, N = 2^q, τ = r + 2, c = (τ + r/2 − 1)/2, and u = τ − c = r/4 + 3/2. The N shared coordinates can be indexed by subsets S of a q-element set. Set a = |S| and ε = 1 when q − a is even, and ε = 0 otherwise; put j = a + ε. Then 0 ≤ j ≤ r and j has the parity of r. There are binom(q, a) labels at each cardinality a. Consequently, for every j of the parity of r, the ε = 0 multiplicity is binom(q, j), and the ε = 1 multiplicity is binom(q, j − 1), with the latter zero at j = 0. Their sum is binom(r, j) by Pascal's identity. This identification retains the source labels, including the endpoint fibers.")),
                    Paragraph(Text(
                        "On those same coordinates take A₀ = B₀ = diag(u + a), A₁ = diag(c + ε), and B₁ = diag(c + 1 − ε). Since j − ε = a, the common A₀ and B₀ entry is exactly τ + j − c − ε as in the source construction. All entries are positive. All four matrices commute, and the two marks occur equally often: the q-th forward difference of the constant function is zero for q > 0. Thus the lists of entries of A₁ and B₁ agree with multiplicity. Equality of their diagonal characteristic polynomials expresses the same native spectral condition used in the claim.")),
                    Paragraph(Text(
                        "For a finite ordered word s with m zero letters and n one letters, word_diagonal identifies the native product with the diagonal of the pointwise monomials, including m = n = 0 for the empty word. Splitting the two marks gives tr Πs(A) − tr Πs(B) = ((c + 1)^n − c^n) Δ^q(x ↦ x^m)(u). The signed binomial formula is fwdDiff_iter_eq_sum_shift. The finite-difference mean-value theorem exists_fwd_diff_iter_eq_iterated_deriv, together with the nonnegative derivatives of a natural power on x > 0, gives Δ^q(x ↦ x^m)(u) ≥ 0. All word traces are real and nonnegative, so this difference yields domination of the absolute B-trace; n = 0 gives equality.")),
                    Paragraph(Text(
                        "For any real function f, Pascal's identity applied to the two marked coordinate classes gives Σi f((A₀ + A₁)ii) = Σj≡r binom(r, j) f(τ + j), and Σi f((B₀ + B₁)ii) = Σj≢r binom(r, j) f(τ + j), with 0 ≤ j ≤ r. In particular their real-power sums differ by Δ^r(x ↦ x^p)(τ). This is a relation of the actual two sums of the same four matrices. Entrywise real continuous functional calculus, supplied by cfc_diagonal, identifies these scalar sums with the native power traces. For every integer 1 ≤ ℓ ≤ q, fwdDiff_iter_pow_eq_zero_of_lt makes the difference zero.")),
                    Paragraph(Text(
                        "For k < p < k + 1, the r-th derivative coefficient p(p − 1)⋯(p − r + 1) has exactly one negative factor. The pinned formula Real.iter_deriv_rpow_const and its descending-Pochhammer product interface give this derivative without a new scalar derivative theory. The finite-difference mean-value theorem then makes the difference strictly negative. For the shifted first branch, 2·3^p + 6^p − 2^p − 2·5^p equals Δ²(x ↦ x^p)(4) − Δ²(x ↦ x^p)(2), which is also Δ³(x ↦ x^p)(2) + Δ³(x ↦ x^p)(3). Both summands are negative throughout 1 < p < 2. At p = 1 and p = 2 the first-branch difference vanishes. For the first-branch word counts m,n ≥ 0, the A-trace minus the B-trace is (3^m − 2^m)(3^n − 2^n) − (2^m − 1)(2^n − 1). Convexity gives 3^m − 2^m ≥ 2^m − 1 ≥ 0 and the same inequalities for n, so this difference is nonnegative, including either zero count.")),
                    Paragraph(Text(
                        "The native norm_diagonal identity turns each power-sum comparison into the corresponding unnormalised finite Schatten comparison. This is the unnormalised finite norm defined in Holder. For the higher family, ΣS |S| = q·2^(q−1) and Σε = N/2. Hence every individual trace is T = (c + 1/2)N: tr A₀ = τN + (r/2)N − cN − N/2 = T, while tr A₁ = tr B₁ = T. The first branch has T = 8. In both branches T > 0. With the single real γ = 1/T, replace each matrix X by γX. Every individual trace becomes one. Each ordered word product, and therefore its trace, is multiplied by γ^L for its length L, including L = 0; each sum is multiplied by γ. Positivity, commutativity, paired spectra, all-word domination, every stated integer power-trace equality, and the reversal on the entire open interval are retained. The two positive endpoint orders k and k + 1 therefore have equal norms.")),
                    Paragraph(Text(
                        "This application concerns the normalization of these positive-trace source families; it does not normalize arbitrary zero-trace positive semidefinite data. It supplies the noninteger witness relation in the repository's exponent-boundary construction. The whole equivalence for U(p) also needs the separate integer-order implication for arbitrary finite dimension, including dimension zero, from the general ordered-word expansion. The application makes no claim about the infinite exponent, minimum dimension, fixed-dimension optimality, tensor-product spin families, strong alignment, entropy, or an external conjecture. The unshifted three-halves refutation above remains its stated result; these consequences use the indicated common-coordinate construction and existing diagonal, binomial, and finite-difference interfaces."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("alhejji-knill-2024-fractional-schatten-alignment"),
                    ResolutionKind.Refuted)))));

    private static Formula ClaimBody()
    {
        Formula aTrace = WordTrace("a₀", "a₁");
        Formula bTrace = WordTrace("b₀", "b₁");
        Formula wordBound = All("s", At(Qualified("List"), Qualified("Bool")),
            Conjunction(
                Equal(At(Qualified("Complex", "im"), aTrace), Typed(D(0), Reals())),
                LE(new Formula.Norm(bTrace), At(Qualified("Complex", "re"), aTrace))));
        Formula normBound = All("p", Reals(), Arrow(LE(Typed(D(1), Reals()), X("p")),
            LE(Schatten(Add(X("b₀"), X("b₁"))), Schatten(Add(X("a₀"), X("a₁"))))));
        return All("m", Naturals(), All("a₀", MatrixType(), All("a₁", MatrixType(),
            All("b₀", MatrixType(), All("b₁", MatrixType(),
                Arrow(Positive("a₀"), Arrow(Positive("a₁"), Arrow(Positive("b₀"),
                    Arrow(Positive("b₁"),
                        Arrow(Equal(Charpoly("a₀"), Charpoly("b₀")),
                            Arrow(Equal(Charpoly("a₁"), Charpoly("b₁")),
                                Arrow(wordBound, normBound))))))))))));
    }

    private static Formula WordTrace(string zero, string one) => At(Qualified("Matrix", "trace"),
        At(Qualified("D5", "S3", "Observer", "Hankel", "WordHankelRealization", "wordProduct"),
            LambdaOf("b", Qualified("Bool"), At(Qualified("ite"),
                Equal(X("b"), Qualified("Bool", "true")), X(one), X(zero))), X("s")));
    private static Formula Positive(string name) => At(Qualified("Matrix", "PosSemidef"), X(name));
    private static Formula Charpoly(string name) => At(Qualified("Matrix", "charpoly"), X(name));
    private static Formula Schatten(Formula matrix) =>
        At(Qualified("schattenNorm"), matrix, X("p"));
    private static Formula MatrixType() => At(Qualified("Matrix"),
        At(Qualified("Fin"), X("m")), At(Qualified("Fin"), X("m")), Complexes());
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "Schatten", "FractionalSchattenAlignmentRefutation", name);
    private static Formula X(string name) => name switch
    {
        "a₀" => new Formula.Subscript(F.Id("a"), D(0)),
        "a₁" => new Formula.Subscript(F.Id("a"), D(1)),
        "b₀" => new Formula.Subscript(F.Id("b"), D(0)),
        "b₁" => new Formula.Subscript(F.Id("b"), D(1)),
        _ => F.Id(name),
    };
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
