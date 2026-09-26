using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class LatinEulerianMultiplesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/LatinEulerianMultiples.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/mirzavaziri2026latin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every permitted interior multiple of the order occurs as the total column-ascent number of a Latin square.",
        H("Interior Multiples of the Latin Eulerian Total"),
        Blocks(
            Node("result", "Every interior multiple occurs", "result", ResultFormula(),
                "For every n at least five and every k between two and n minus three, there is an order-n Latin square with total ascent number k n.",
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("mirzavaziri-yaqubi-latin-eulerian-multiples"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem, resolution);

    private static Formula ResultFormula() => Disp(F.Id("claim"));
}
