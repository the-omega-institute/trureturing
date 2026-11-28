using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.MixedModel;

internal sealed class EquivariantCoefficientsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equivariant Coefficients", H("Equivariant Coefficients"),
        Blocks(
            Paragraph(Text("Archimedean Tate integral of slices of a rapid datum converges and is rapid. Mixed-model slice of a Schwartz-Bruhat datum as partial Fourier transform at places S. Finite slices of standard framed data along an isotropic subspace. Unit law of a tame character; idele of inverse uniformisers and its modulus. Fourier coefficient as functional of local datum, laws under shears and centre.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/MixedModel/EquivariantCoefficients.exists_linear_centreCoeff"),
                H("exists_linear_centreCoeff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("At each point x, Ψ ↦ (T-th Fourier coefficient of 𝒟Ψ) is a linear functional L on M. The shear of Ψ by z along the frame k at x stays in M and multiplies LΨ by ψ(tr(T_S z)), T_S = T divided by the idele invDifferentIdele, read at the ramified places S of 𝔠.")))))));
}
