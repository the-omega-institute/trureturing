using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.ChargedResidue;

internal sealed class FiniteChambersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Supported formal collision residues.",
        H("FiniteChambers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("charged-residue-finite-chambers-scalar"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/ChargedResidue/FiniteChambers.native_chamber_scalar_full"),
                H("The two finite ordered contraction sums"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("Each contraction chamber has its own natural range. A supported sparse quadratic convolution identifies each ordered sum with its signed chamber coefficient. The signed difference is evaluated by the two-pole formula, keeping both negative-degree tests. The identity is used in the actual complete residue diagonal for arbitrary translated input monomials."))),
                DescribeRole.Theorem))));
}
