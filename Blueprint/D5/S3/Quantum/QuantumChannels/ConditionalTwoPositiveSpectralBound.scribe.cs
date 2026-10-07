using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class ConditionalTwoPositiveSpectralBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/ConditionalTwoPositiveSpectralBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/vomende2025twopositivebound");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ConditionalTwoPositiveSpectralBound for the spectral bound of conditionally two-positive maps.",
        H("ConditionalTwoPositiveSpectralBound"),
        Blocks(
            Node("expend", "expEnd", "expEnd",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(Named("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("L"), Sp, Colon, Sp, Parenthesized(Seq(Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, Named("d"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, Named("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, new Formula.Subscript(To, Seq(F.Id("l"), OpenBracket, Seq(Mathbb, Grp(F.Id("C"))), CloseBracket)), Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, Named("d"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, Named("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, Named("expEnd"), Sp, Named("L"), Sp, Named("t"), Sp, Eq, Sp, Parenthesized(Seq(Named("NormedSpace"), Sp, Dot, Sp, Named("exp"), Sp, Parenthesized(Seq(Named("t"), Sp, Cdot, Sp, Named("L"), Sp, Dot, Sp, Named("toContinuousLinearMap"))))), Sp, Dot, Sp, Named("toLinearMap"))),
                "The operator exponential of t times the continuous-linear realization of L, returned as a complex-linear endomorphism. Finite dimensionality gives the continuous-linear realization without an additional hypothesis.", DescribeRole.Definition, Repo()),
            Node("conditionallytwopositive", "ConditionallyTwoPositive", "ConditionallyTwoPositive",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(Named("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("L"), Sp, Colon, Sp, Parenthesized(Seq(Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, Named("d"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, Named("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, new Formula.Subscript(To, Seq(F.Id("l"), OpenBracket, Seq(Mathbb, Grp(F.Id("C"))), CloseBracket)), Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, Named("d"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, Named("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Comma, Sp, Named("ConditionallyTwoPositive"), Sp, Named("L"), Sp, Leftrightarrow, Sp, Forall, Sp, Named("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Comma, Sp, D(0), Sp, Leq, Sp, Named("t"), Sp, To, Sp, Parenthesized(Seq(Named("KPositive"), Sp, D(2), Sp, Named("d"), Sp, Parenthesized(Seq(Named("expEnd"), Sp, Named("L"), Sp, Named("t"))))))),
                "Page 11, arXiv:2506.02145v1: \"A map L is called conditionally 2-positive if e^{tL} is 2-positive for all t \u2265 0.\" KPositive 2 is positivity of MatrixMap.kron LinearMap.id with the map, on matrices indexed by Fin 2 \u00d7 Fin d; expEnd is the operator exponential of the same endomorphism.", DescribeRole.Definition, Lit()),
            Node("claim", "claim", "claim",
                Disp(Seq(Named("claim"), Sp, Leftrightarrow, Sp, Forall, Sp, Parenthesized(Seq(Named("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, D(0), Sp, Lt, Sp, Named("d"), Sp, To, Sp, Forall, Sp, Named("L"), Sp, Colon, Sp, Parenthesized(Seq(Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, Named("d"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, Named("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, new Formula.Subscript(To, Seq(F.Id("l"), OpenBracket, Seq(Mathbb, Grp(F.Id("C"))), CloseBracket)), Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, Named("d"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, Named("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Named("ConditionallyTwoPositive"), Sp, Named("L"), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Named("LinearMap"), Sp, Dot, Sp, Named("trace"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Parenthesized(Seq(Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, Named("d"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, Named("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Named("L")))), Sp, Dot, Sp, Named("im"), Sp, Eq, Sp, D(0), Sp, Land, Sp, Named("spectralBound"), Sp, Named("L"))),
                "Page 11, arXiv:2506.02145v1: \"Hence one may wonder whether all (generators of) completely positive maps, resp. 2-positive maps satisfy\" tr(\u03a6) \u2264 d min \u211c(\u03c3(\u03a6)) + (d\u00b2 \u2212 d) max \u211c(\u03c3(\u03a6)) ? \"With this, (10) becomes really a conjecture about the spectrum of arbitrary conditionally 2-positive maps.\" The encoding quantifies over every positive matrix dimension and every complex-linear endomorphism, uses the literal operator exponential, and takes the real extrema over the roots of its characteristic polynomial. It also asserts that the endomorphism trace is real.", DescribeRole.Definition, Repo()),
            Node("result", "result", "result",
                Disp(Named("claim")),
                "Every conditionally 2-positive endomorphism satisfies (10). Adding epsilon times the trace-to-identity map produces a faithful Perron eigenmatrix. Congruence by its square root and division by the Perron eigenvalue give a unital map whose Hilbert\u2013Schmidt adjoint is trace preserving. Theorem 1 transports through this similarity. Letting epsilon tend to zero gives the bound for every 2-positive map; applying it to exp(tL) and passing through the difference quotient at t = 0 gives the asserted bound for L, together with reality of its trace.", DescribeRole.Theorem, Repo()))));

    private static AssessedProvenance Lit() => AssessedProvenance.FromLiterature(Source);
    private static AssessedProvenance Repo() => AssessedProvenance.FromRepo(Source);
    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
}
