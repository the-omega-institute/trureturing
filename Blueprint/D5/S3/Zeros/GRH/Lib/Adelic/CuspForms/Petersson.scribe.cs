using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.CuspForms;

internal sealed class PeterssonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Petersson", H("Petersson"),
        Blocks(
            Paragraph(Text("Every conjugate of a small ball in U(J) contains a dilation along an isotropic subspace. After a rational translation, the pair's operator norm is bounded by a height power. Bounded forms of integrable discrete series type are cuspidal. Petersson product: invariance, self-adjoint projector, rank-one action on real translates of forms.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/Petersson.petersson_realConv_realConv"),
                H("petersson_realConv_realConv"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a cusp kernel e on G_∞, forms F, F' of type e and α, β integrable on G_∞, ⟨R(α)F, R(β)F'⟩ equals ⟨F, F'⟩ times ∫∫ conj(α(x)) β(y) conj(e(x⁻¹y))/e(1) dy dx.")))))));
}
