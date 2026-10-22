using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum;

internal sealed class IntegralDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native integral weights and oscillator negation",
        H("The odd oscillator sector"),
        Blocks(
            Paragraph(Text("The actual involution S is TensorProduct.map sigmaLinear id on the original tensor carrier. Its coefficient at occupation d is multiplied by (-1) raised to W(d). The oscillator count and W differ by twice the finite mode-weight sum, so this is also the sign given by the original occurrence enumeration.")),
            Describe.Lean(
                DescribeId.Create("native-half-fock-integral-odd-sector"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockNativeSpectrum/Integral.integral_supremum"),
                H("All integer eigenspaces generate exactly ker(S+id)"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("At rank twenty-four, equality of the original weight with integer n is equivalent to W=2n-3. Therefore integer homogeneous states have odd W and lie in ker(S+id). Conversely an odd-sector state has no even occupation coefficients; its finite natural-weight reconstruction places every nonzero summand in an integer eigenspace. This proves the submodule equality on every original state."))),
                DescribeRole.Theorem),
            Paragraph(Text("integer_below_two proves that every integer eigenspace below two is zero. Bare S-fixed ground states have weight 3/2, so S=+1 is not the integer sector. One may describe the same odd sector as fixed by the explicit negative lift -S, but an oscillator conjugation identity alone does not choose an orbifold lift.")),
            Paragraph(Text("The spectral-sector equality does not itself assert a complete twisted module Jacobi law, realized moonshine gluing, fusion or anomaly triviality. Those identities are separate mathematical obligations.")))));
}
