using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class BinaryCubePartialShellDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubePartialShell";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The adjacency image of a partial shell counts the pairs of selected and omitted directions and the center parity.",
        H("Binary adjacency of a partial neighbor shell"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("shell-word"),
                DeclarationHandle.Create(Module + ".shellWord"),
                H("Indicator of a partial shell"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The word is one at the neighbors reached from the center in a selected direction " +
                        "and zero at every other vertex."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("partial-shell-outside-card"),
                DeclarationHandle.Create(Module + ".partial_shell_outside_card"),
                H("The image away from the center counts selected–omitted pairs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In dimension n choose s coordinate directions at a center and take the binary indicator of " +
                        "those s neighbors. Away from the center, the adjacency image is supported precisely on " +
                        "double flips in one selected and one omitted direction. Each such pair gives a distinct " +
                        "site, so the support away from the center has size s(n − s)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partial-shell-image-card"),
                DeclarationHandle.Create(Module + ".partial_shell_image_card"),
                H("Exact image weight of a partial shell"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The full image has weight s(n − s) plus the residue of s modulo two. The coefficient at the " +
                        "center is the sum of the s selected neighbors in the binary field."))),
                DescribeRole.Theorem)),
        []));
}
