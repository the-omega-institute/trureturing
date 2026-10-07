using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class P13CatalyticHDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/P13CatalyticH.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual P13 matching series satisfies the rational catalytic H bridge.",
        H("The catalytic change of variables in Rational[t][[q]]"),
        Blocks(
            Node("p13-p13catalytich-q", "Outer variable", "q",
                "q is the outer power-series variable in the coefficientwise formal series ring.", DescribeRole.Definition),
            Node("p13-p13catalytich-zeta", "Catalytic point", "zeta",
                "zeta=q/(1+q)^2 is evaluated only through the HasEval outer-series API.", DescribeRole.Definition),
            Node("p13-p13catalytich-u", "Inner change of variables", "u",
                "u(t)=(1+q)(1-t)/(1-qt), with the denominator inverted by the existing unit inverse over polynomial coefficients.", DescribeRole.Definition),
            Node("p13-p13catalytich-aq", "Actual matching carrier", "Aq",
                "Aq is actualSeries from the original P13-avoiding perfect-matching carrier, evaluated at zeta.", DescribeRole.Definition),
            Node("p13-p13catalytich-bridge", "Actual H bridge", "catalytic_H_bridge",
                "The public theorem proves the units 1+q, 1-qt, and 1-q^2t, specializes the reciprocal marker to u(qt), proves the kernel and zeta*u^2 identities, and derives q(1-t)^2 H(qt)+delta*t H=C(Aq-1)(1+qt^2)+(C^2-4qAq)t from the public actual F equation by legitimate evaluation composition.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
