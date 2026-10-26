using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.ChargedResidue;

internal sealed class SupportedResidueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Supported formal collision residues.",
        H("SupportedResidue"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("charged-residue-supported-residue-diagonal"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/ChargedResidue/SupportedResidue.chargedPhysicalResidueRow_collision_diagonal"),
                H("The actual residue on the common collision diagonal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("For every original lattice, unit determinant, charges, signs, matching integer lifts and signed indices, the complete physical residue on an arbitrary oscillator tensor an actual ground vector equals the sum over its genuine pair-translated polynomial support with the two-pole scalar weights. Each whole ordered sum is enlarged by its own field order before monomial expansion. The two scalar chambers are then combined; neither ordered half is asserted to vanish."))),
                DescribeRole.Theorem))));
}
