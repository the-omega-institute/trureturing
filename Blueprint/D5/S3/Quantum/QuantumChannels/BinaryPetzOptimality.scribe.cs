using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class BinaryPetzOptimalityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/BinaryPetzOptimality";
    private static LibraryNoteRef Reversal =>
        LibraryNoteRef.Create("D5/L/Quantum/barnumknill2002reversal");
    private static LibraryNoteRef Collision =>
        LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary Petz optimality for finite quantum records",
        H("Binary Petz optimality for finite quantum records"),
        Blocks(
            Describe.Lean(DescribeId.Create("binarypetzoptimality-block-criterion"),
                DeclarationHandle.Create(Module + ".binary_petz_is_optimal_iff"),
                H("Optimality from the visible blocks"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Reversal),
                Blocks(
                    Paragraph(Text("Two rectangular amplitude matrices define the weighted hidden states. Their sum determines the inverse square root on its support. The first Petz effect and its full complement form an admissible binary measurement, including for a singular state sum.")),
                    Paragraph(Text("The completed measurement attains the Helstrom contrast exactly when the two diagonal visible Gram blocks intertwine through the off-diagonal cross block."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("binarypetzoptimality-periodic-record"),
                DeclarationHandle.Create(Module + ".ring_physical_petz_is_optimal_iff"),
                H("Exact periodic record criterion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Reversal, Collision),
                Blocks(
                    Paragraph(Text("For the two fair-prior complementary states of the primitive periodic collision, the transposed support Petz effect minimizes the physical discrimination error precisely when the total ring length is divisible by four. The statement applies in the common-marginal range from seven sites onward.")),
                    Paragraph(Text("The finite ring enters through its actual partial trace and exact cross reduction. The error criterion concerns a static binary measurement."))),
                DescribeRole.Theorem))));
}
