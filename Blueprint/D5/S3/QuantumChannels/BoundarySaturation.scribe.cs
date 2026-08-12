using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class BoundarySaturationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Positive semidefiniteness of the 2x2 complete-positivity matrix [[1,z],[conj z,p]] forces the coherence boundary ratio |z|^2 <= p, with equality exactly at the singular CP boundary.",
        H("CP Boundary Saturation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cp-boundary-ratio-le-one"),
                DeclarationHandle.Create("D5/S3/QuantumChannels/BoundarySaturation.cp_boundary_ratio_le_one"),
                H("The CP matrix bounds the coherence boundary ratio"),
                StatementSource.FromAuthor(Disp(Seq(
                    Lvert, Sp, F.Id("z"), Sp, Rvert, Caret, Grp(D(2)), Sp, Le, Sp, F.Id("p")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a channel with a pure fixed point, let z = lambda_coh and p = lambda_pop be the "
                        + "coherence and population decay factors in the tangent space. The 2x2 complete-positivity "
                        + "matrix [[1, z], [conj z, p]] is Hermitian, and its determinant is p - |z|^2. Positive "
                        + "semidefiniteness gives a nonnegative determinant, hence the coherence RLD boundary ratio "
                        + "|z|^2 / p is at most one, i.e. |z|^2 <= p.")),
                    Paragraph(Text(
                        "Equality |z|^2 = p holds exactly when the determinant vanishes, i.e. when the CP matrix is "
                        + "singular -- the channel sits at the complete-positivity boundary. No claim is made about "
                        + "the RLD contraction ratio itself beyond this boundary criterion."))),
                DescribeRole.Theorem))));
}
