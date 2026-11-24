using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ArithmeticRamsey;

internal sealed class RadoLastBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArithmeticRamsey/RadoLastBoundary.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/hughes2026radolastexception");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit two-colouring avoids the boundary equation for every k at least three.",
        H("Boundary colourings for the last Rado exception"),
        Blocks(
            Node("boundary-lb", "The lower-bound expression", "LB",
                "LB(c,k) is the natural-number ceiling expression used for the two-colour lower bound.", DescribeRole.Definition),
            Node("boundary-cstar", "The last-exception parameter", "cstar",
                "cstar(k) is k(k^2+k-4)/2 for odd k and k(k^2-2)/2 for even k.", DescribeRole.Definition),
            Node("boundary-col-odd", "Odd residue colouring", "colOdd",
                "For odd k, the colouring is one on the prescribed nonzero residue interval and on the sufficiently large zero residue class.", DescribeRole.Definition),
            Node("boundary-col-even", "Even block colouring", "colEven",
                "For even k, the colouring marks the exceptional singleton and the terminal block around k(k-2)/2.", DescribeRole.Definition),
            Node("boundary-existence", "The boundary avoiding colouring", "exists_good_col_cstar",
                "For every k at least three, the explicit colouring has no monochromatic solution of x + y + cstar(k) = k z on [1,LB(cstar(k),k)]. Repeated variables remain allowed; no finite boundary Rado-number existence is asserted.", DescribeRole.Theorem))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
