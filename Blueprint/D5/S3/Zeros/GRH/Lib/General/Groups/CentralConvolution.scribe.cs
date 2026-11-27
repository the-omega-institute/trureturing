using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Groups;

internal sealed class CentralConvolutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Central Convolution", H("Central Convolution"),
        Blocks(
            Paragraph(Text("Central projections of a group algebra act as orthogonal projections; convolution contracts.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Groups/CentralConvolution.sum_norm_conv_le"),
                H("sum_norm_conv_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Convolution with a central self-adjoint idempotent e of ℂ[G], along a homomorphism φ : G → H of finite groups, is a contraction of ℓ²(H, V): ∑_s ‖∑_t e(t) f(φ(t)⁻¹ s)‖² ≤ ∑_s ‖f(s)‖².")))))));
}
