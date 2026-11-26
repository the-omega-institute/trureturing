using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class LabelResetSupportDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Decoherence/LabelResetSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Isometric padding and support transfer for finite matrix marginals.",
        H("Support geometry for finite label reset"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-extension-of-isometries"),
                DeclarationHandle.Create(Module + "exists_unitary_extension"),
                H("Extension with prescribed column action"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("If V and W are isometries from the same finite coordinate space to the same ambient space, an ambient unitary U satisfies UV = W. The proof first matches their projections by spectral conjugacy and then fixes the map on the columns."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("support-from-retained-marginal"),
                DeclarationHandle.Create(Module + "supported_of_marginal"),
                H("A positive joint state inherits the retained support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/mohammady2016minimising"), LibraryNoteRef.Create("D5/L/Entropy/reeb2014improved")),
                Blocks(
                    Paragraph(Text("If the retained marginal of a positive semidefinite joint matrix is VσV*, its joint support lies in the image of I⊗V. Compression with I⊗V recovers the joint matrix in those support coordinates. The trace of the positive compression on the complementary subspace vanishes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("factor-pure-label-marginal"),
                DeclarationHandle.Create(Module + "pure_marginal_factors"),
                H("A prescribed pure marginal factors off"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/mohammady2016minimising")),
                Blocks(
                    Paragraph(Text("A positive semidefinite matrix whose label marginal is the projector of the prescribed normalized vector factors as that projector tensored with its remaining marginal."))),
                DescribeRole.Theorem))));
}
