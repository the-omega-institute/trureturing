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
            Describe.Lean(DescribeId.Create("boseroottranspose-partialtranspose-composition"),
                DeclarationHandle.Create(Prefix + "partialTranspose_composition"),
                H("partialTranspose composition"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Composing product-basis partial transposes replaces the cut by its symmetric difference. The identity holds for arbitrary matrices and all cuts."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("boseroottranspose-pairroottranspose"),
                DeclarationHandle.Create(Prefix + "pairRootTranspose"),
                H("pairRootTranspose"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transpose the first member of the actual ordered pair, keeping the second member unchanged."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("boseroottranspose-marginal-roottranspose"),
                DeclarationHandle.Create(Prefix + "marginal_rootTranspose"),
                H("marginal rootTranspose"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For distinct root and leaf, the actual root partial transpose commutes with the root-leaf partial trace and transposes the first factor of that marginal."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("boseroottranspose-star-roottranspose-iff"),
                DeclarationHandle.Create(Prefix + "star_rootTranspose_iff"),
                H("star rootTranspose iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Root partial transpose is an involutive bijection of fully PPT star witnesses for an arbitrary input and its first-factor transpose. The leaf sandwich is retained. Symmetric-difference cuts include ordinary and full-transpose endpoints, whose positivity is supplied explicitly."))),
                DescribeRole.Theorem))));
}
