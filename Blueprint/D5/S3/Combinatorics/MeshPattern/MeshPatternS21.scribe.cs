using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MeshPattern;

internal sealed class MeshPatternS21Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MeshPattern/MeshPatternS21.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/lvzhang2025mesh");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mesh patterns 123 and 321 with the common shading R = {0,1,2} squared together with {(3,3)} have a symmetric joint occurrence distribution.",
        H("Joint Symmetry of the Mesh Pattern Pair S21"),
        Blocks(
            Node("mesh-pattern-s21-result", "Joint equidistribution", "result", "For all nonnegative integers n, k and l, the number of permutations of one through n having k occurrences of the mesh pattern 123 and l occurrences of the mesh pattern 321 equals the number having l occurrences of 123 and k occurrences of 321, where both patterns have shading R = {0,1,2} squared together with {(3,3)}.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
