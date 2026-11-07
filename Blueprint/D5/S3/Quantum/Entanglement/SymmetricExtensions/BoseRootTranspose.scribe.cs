using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SymmetricExtensions;

internal sealed class BoseRootTransposeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Root partial transpose of actual star witnesses", H("Root partial transpose of actual star witnesses"),
        Blocks(
            Paragraph(Text("Finite register and local-label types use the original product basis. This is the root-transpose transport underlying the CLDUI companion application in Haobo Ma and Wenlin Zhang's note. The GNP cone characterization is proved separately in BoseHierarchy. Full Bose support is not asserted for a companion witness.")),
            Describe.Lean(DescribeId.Create("boseroottranspose-allcutsppt"),
                DeclarationHandle.Create(Prefix + "AllCutsPPT"),
                H("AllCutsPPT"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positivity is required at every subset, including the ordinary empty cut and full transpose. For a positive input this is equivalent to the existing FullyPPT predicate."))),
                DescribeRole.Definition),
            Paragraph(Text("Product-basis partial transposes compose by symmetric difference for arbitrary matrices and all cuts. The root transpose commutes with each distinct root-leaf partial trace and transposes the first pair factor. Applying the transport twice restores the original matrix and witness, so the leaf sandwich and the ordinary and full-transpose positivity endpoints are retained for every finite register and local-label type.")),
            Describe.Lean(DescribeId.Create("boseroottranspose-pairroottranspose"),
                DeclarationHandle.Create(Prefix + "pairRootTranspose"),
                H("pairRootTranspose"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transpose the first member of the actual ordered pair, keeping the second member unchanged."))),
                DescribeRole.Definition),
            Paragraph(Text("Root partial transpose is an involutive transport of fully PPT star witnesses for an arbitrary input and its first-factor transpose. The leaf sandwich is retained, and symmetric-difference cuts include the ordinary and full-transpose endpoints with their positive semidefinite witnesses.")))));
}
