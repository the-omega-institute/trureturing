using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class TraceExpExponentialConvexityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Divergence/TraceExpExponentialConvexityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/briet2009jensenshannon");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The trace exponential fails exponential convexity on density matrices, already on four qubit states.",
        H("The trace exponential is not exponentially convex"),
        Blocks(
            SourceQuotation(),
            Entry("trace-exp", "trExp", "The trace exponential", TraceExp(),
                "The function takes the trace of the matrix exponential over the complex numbers. "
                + "For Hermitian inputs its value is real.", DescribeRole.Definition, true),
            Entry("density", "IsDensity", "Density matrices", Density(),
                "A density matrix is positive semidefinite and has trace one.",
                DescribeRole.Definition, true),
            Entry("claim", "claim", "Exponential convexity on density matrices", Claim(),
                "Definition 4 requires the midpoint kernel to be positive definite. "
                + "For every finite family of density matrices and every real coefficient vector, "
                + "the real part of its quadratic form must therefore be nonnegative.",
                DescribeRole.Definition, true),
            Entry("temperature-family", "family", "Failure at every nonzero inverse temperature", Family(),
                "Let ρ₀=I/2 and let ρ₁,ρ₂,ρ₃ be the rank-one projectors onto "
                + "(1,0), (1/2,√3/2), and (−1/2,√3/2). Set u=e^(t/4)>0. "
                + "Explicit rotations diagonalize their pairwise sums. The kernel values are "
                + "K₀₀=2u², Kₖₖ=u⁴+1 for k>0, and Kᵢⱼ=u³+u for i≠j. "
                + "With c=(−3(u+u⁻¹)/2,1,1,1), the quadratic form equals −(3/2)(u−1)⁴. "
                + "Injectivity of the real exponential makes this strictly negative for t≠0. "
                + "Replacing t by −t also refutes the kernels Tr exp(−t(ρ+σ)/2).",
                DescribeRole.Theorem, false),
            Entry("refutation", "result", "A centre-plus-trine counterexample", Disp(Seq(Neg, Sp, V("claim"))),
                "The temperature family at t=1 contradicts exponential convexity of A↦Tr(e^A) "
                + "on density matrices. One maximally mixed qubit state and three pure states suffice. "
                + "The proposed argument for Hilbert-space embeddability through this conjecture "
                + "cannot apply. Hilbert-space embeddability of the square root of quantum "
                + "Jensen–Shannon divergence in dimensions at least three is not settled by this result.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock SourceQuotation() => Paragraph(Text(
        "Jop Briët and Peter Harremoës, Properties of classical and quantum Jensen-Shannon divergence, "
        + "Physical Review A 79, 052311 (2009), DOI 10.1103/PhysRevA.79.052311, arXiv:0806.4472v4. "
        + "Definition 4 (Exponential convexity), verbatim: "
        + "“Let X be a convex set and φ : X → R a mapping. Then φ is said to be exponentially convex "
        + "if the function X × X → R given by (x, y) → φ((x+y)/2) is positive definite.” "
        + "§VI (Conclusions and open problems), verbatim: "
        + "“Whether (QJD1)^{1/2} is a metric for all mixed states remains unknown. However, based on a large "
        + "amount of numerical evidence, we conjecture the function A → Tr(e^A) to be exponentially convex "
        + "for density matrices A. Proving this would imply that QJDα is negative definite for α ∈ (0, 2], "
        + "and hence the square of a metric that can be embedded in a real Hilbert space.”"));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("briet-harremoes-2009-trace-exp-exponential-convexity"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Scale(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Mat(Formula n) => Call("Matrix", Call("Fin", n), Call("Fin", n), Complex);
    private static Formula StateFamily(Formula n, Formula count) => Arrow(Call("Fin", count), Mat(n));
    private static Formula CoeffFamily(Formula count) => Arrow(Call("Fin", count), Real);
    private static Formula Densities(Formula count) =>
        All("i", Call("Fin", count), Call("IsDensity", Call("rho", V("i"))));
    private static Formula Quadratic(Formula scale) => Call("re", Seq(
        Sum, Underscore, Grp(V("i")), Sp, Sum, Underscore, Grp(V("j")), Sp,
        Parenthesized(Mul(Call("ofReal", Mul(Call("c", V("i")), Call("c", V("j")))),
            Call("trExp", Scale(scale, Add(Call("rho", V("i")), Call("rho", V("j")))))))));

    private static Formula TraceExp() => Disp(All("n", Nat, All("A", Mat(V("n")),
        Eq(Call("trExp", V("A")), Call("trace", Call("exp", V("A")))))));
    private static Formula Density() => Disp(All("n", Nat, All("rho", Mat(V("n")),
        Iff(Call("IsDensity", V("rho")),
            And(Call("PosSemidef", V("rho")), Eq(Call("trace", V("rho")), D(1)))))));
    private static Formula Claim() => Disp(Iff(V("claim"),
        All("n", Nat, All("N", Nat,
            All("rho", StateFamily(V("n"), V("N")), All("c", CoeffFamily(V("N")),
                Imp(Densities(V("N")), Le(D(0), Quadratic(new Formula.Fraction(D(1), D(2)))))))))));
    private static Formula Family() => Disp(All("t", Real,
        Imp(Seq(V("t"), Sp, Neq, Sp, D(0)),
            Some("rho", StateFamily(D(2), D(4)), Some("c", CoeffFamily(D(4)),
                And(Densities(D(4)), Lt(Quadratic(Call("ofReal", new Formula.Fraction(V("t"), D(2)))), D(0))))))));
}
