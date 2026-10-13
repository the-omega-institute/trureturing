using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Optimization;

internal sealed class WeightedCrownFirstLevelGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Optimization/WeightedCrownFirstLevelGap.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/takahashietal2023su2sdp");
    private static readonly Formula N = F.Id("n"), X = F.Id("x");
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(name, Colon, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula OverN(Formula f) => All(N, Nat(), f);
    private static Formula Hamiltonian() => Call("crownH", N, X);
    private static Formula Region(Formula f) => OverN(Imp(Le(D(3), N), All(X, Real(), Imp(Lt(Call("L", N), X), Imp(Lt(X, Call("U", N)), f)))));
    private static Formula Claim() => Region(Lt(Call("lambdaMax", Hamiltonian()), Call("npa1Value", N, X)));
    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("weighted-crown-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first-level SDP is inexact throughout the open weighted-crown interval.",
        H("First-level inexactness on the weighted-crown interval"), Blocks(
            Node("claim", "The open weighted-crown interval", Eq(F.Id("claim"),Parenthesized(Claim())),
                "Appendix C.1, printed p. 33, verbatim: \"The intermediate region (n + 2)\u00b2/4(n + 1) < x < (n + 2)/3 is left as an open problem, although numerics strongly suggest that SDP indeed fails in that region.\" The encoding quantifies every n \u2265 3 and every real x in the displayed open interval, and compares the nonzero-vector Rayleigh supremum with the real level-one moment optimum.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The first-level SDP is inexact", Claim(),
                "The feasible moment objective is strictly above n+1, while the literal Hamiltonian has Rayleigh supremum at most n+1. The upper interval endpoint is below 1+n/2, so the spectral bound applies to every point of the open interval.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("takahashi-et-al-2023-weighted-crown-npa1-gap"), ResolutionKind.Proved)))));
}
