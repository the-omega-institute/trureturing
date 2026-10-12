using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class CentredGaussianDilationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/CentredGaussianDilationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/faifmanpolterovich2026faberkrahn");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A centred 16-dimensional convex pyramid has non-log-concave Gaussian dilations.",
        H("Centred Gaussian dilation refutation"),
        Blocks(
            SourceQuotation(),
            Entry("gaussian-measure", "gaussianMeasure", "Standard Gaussian measure", Gaussian(),
                "For dimension n, gaussianMeasure n is the finite product of n copies of gaussianReal 0 1 "
                + "on Fin n → R. The coordinates are independent standard real Gaussian variables. "
                + "This is a probability measure, so every set has finite mass.", DescribeRole.Definition, true),
            Entry("convex-body", "IsConvexBody", "A convex body", Body(),
                "A convex body is a real convex compact set with nonempty interior. "
                + "The coordinates Fin n → R carry their usual finite-dimensional topology.",
                DescribeRole.Definition, true),
            Entry("zero-barycenter", "BarycenterZero", "Zero Lebesgue barycenter", Barycenter(),
                "Each coordinate's Lebesgue integral over K is zero. For a convex body the coordinate "
                + "functions are integrable and the volume is positive and finite. Dividing the coordinate "
                + "integrals by that volume therefore gives the usual normalized barycenter at the origin. "
                + "The centering measure here is Lebesgue measure, whereas the dilated masses use Gaussian measure.",
                DescribeRole.Definition, true),
            Entry("scalar-claim", "claim", "Scalar Gaussian dilation concavity", Claim(),
                "The formal encoding of the first clause of Question 5.3 requires the logarithm of the "
                + "Gaussian mass of exp(t) times K to be concave on the entire real line, for every "
                + "dimension and every convex body with zero Lebesgue barycenter. The logarithm is "
                + "applied to the real value of the extended nonnegative Gaussian mass. "
                + "The matrix clause includes this scalar case by taking the symmetric identity matrix.",
                DescribeRole.Definition, true),
            Entry("refutation", "result", "A centred pyramid refutes concavity", Disp(Seq(Neg, Sp, V("claim"))),
                "Let K consist of z in R¹⁶ with −1≤z₀≤16 and |zᵢ|≤10(16−z₀) for i≠0. "
                + "The set is an intersection of linear half-spaces, lies in a bounded box, and contains "
                + "an open neighbourhood of zero. It is consequently a compact convex body with nonempty interior. "
                + "Its transverse slices are symmetric 15-dimensional boxes. Their coordinate integrals vanish "
                + "by negation symmetry. Product integration gives the remaining first moment "
                + "as the integral from −1 to 16 of x[20(16−x)]¹⁵. The antiderivative "
                + "20¹⁵[−(16−x)¹⁶+(16−x)¹⁷/17] has equal endpoint values, so this moment also vanishes. "
                + "The boxes [−1/4,7/2]×[−5,5]¹⁵ and [−1,7/2]×[−5,5]¹⁵ lie in K/4 and K, "
                + "respectively, whereas K/2 lies in the half-space z₀≥−1/2. "
                + "Writing c=(2π)⁻¹ᐟ², the bounds 997/2500<c<2/5 and "
                + "exp(−u²/2)≥1−u²/2+u⁴/8−u⁶/48−5u⁸/1536 for 0≤u≤1 give lower interval masses. "
                + "Gaussian symmetry gives mass 1/2 on each side of zero. The exponential moment "
                + "bounds the positive tails by exp(−a²/2), which is less than 1/350 at a=7/2 "
                + "and less than 1/16000 at a=5. Independence and these rational estimates give "
                + "γ₁₆(K/4)>594/1000, γ₁₆(K)>836/1000 and γ₁₆(K/2)<7/10. "
                + "The quarter-scale pyramid lies inside the half-scale pyramid, ensuring positive middle mass. "
                + "Concavity at −log 4 and zero would require γ₁₆(K/2)²≥γ₁₆(K/4)γ₁₆(K), "
                + "but (7/10)²<(594/1000)(836/1000). This answers both clauses of Question 5.3 "
                + "negatively, with the identity matrix in the second clause. The example has zero Lebesgue "
                + "barycenter; zero Gaussian centroid is a different condition and is unsettled here. "
                + "The smallest dimension permitting a counterexample is also unsettled. "
                + "The author-text locator and quotation are supplied with the statement; independent "
                + "verification of that text and an exhaustive literature or priority claim are ASSUMED-UNVERIFIED.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("faifman-polterovich-2026-centred-gaussian-dilation"),
                ResolutionKind.Refuted) : null);

    private static DocumentBlock SourceQuotation() => Paragraph(Text(
        "Faifman and Polterovich, The Faber–Krahn position of convex bodies and Gaussian measure inequalities, "
        + "arXiv:2607.21539v2, §5.2, p. 38, verbatim: “The B-theorem requires central symmetry. "
        + "To prove Theorem 1.1, we circumvent this by proving a weaker concavity property of the Gaussian "
        + "measure in a special case. However, we do not know a convex counterexample to the B-conjecture "
        + "with its linear barycenter at the origin. Question 5.3. Let K ⊂ R^n be a convex body whose "
        + "Lebesgue barycenter is at the origin. Is t ↦ γ_n(e^t K) log-concave? More generally, is "
        + "t ↦ γ_n(e^{tS} K) log-concave for every symmetric matrix S?”"));

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Natural => Seq(Mathbb, Grp(V("N")));
    private static Formula Coordinates => Seq(Call("Fin", V("n")), Sp, To, Sp, Real);
    private static Formula Sets => Call("Set", Parenthesized(Coordinates));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Equivalent(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));

    private static Formula Gaussian() => Disp(Equal(Call("gaussianMeasure", V("n")),
        Call("pi", Parenthesized(Seq(V("i"), Sp, Mapsto, Sp, Call("gaussianReal", D(0), D(1)))))));
    private static Formula Body() => Disp(Equivalent(Call("IsConvexBody", V("K")),
        And(Call("Convex", Real, V("K")), And(Call("IsCompact", V("K")),
            Call("Nonempty", Call("interior", V("K")))))));
    private static Formula Barycenter() => Disp(Equivalent(Call("BarycenterZero", V("K")),
        All("i", Call("Fin", V("n")), Equal(
            Seq(Int, Underscore, Grp(V("z"), Sp, InMacro, Sp, V("K")), Sp,
                Call("z", V("i")), Sp, V("dz")), D(0)))));
    private static Formula Claim()
    {
        Formula dilation = new Formula.Binary(Call("exp", V("t")),
            FormulaBinaryOperator.Multiply, V("K"));
        Formula mass = Call("toReal", Call("gaussianMeasure", V("n"), dilation));
        Formula function = Parenthesized(Seq(V("t"), Sp, Mapsto, Sp, Call("log", mass)));
        Formula concavity = Call("ConcaveOn", Real, V("univ"), function);
        Formula body = All("n", Natural, All("K", Sets,
            Imp(Call("IsConvexBody", V("K")), Imp(Call("BarycenterZero", V("K")), concavity))));
        return Disp(Equivalent(V("claim"), body));
    }
}
