using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class ThreeFieldFinalInverseCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalInverseCoefficients.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficients of the native inverse", H("Coefficients of the native inverse"), Blocks(
            Describe.Lean(DescribeId.Create("inverse-coefficients"),
                DeclarationHandle.Create(Prefix + "inverse_coefficients"),
                H("inverse_coefficients"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every commutative complex algebra R, every generally infinite three-variable formal series P, all natural k and a, and every native index n, the coefficient at (n0,n1,n2) of chartUnit inverse times nativeChart P equals laurentCoefficient P k a at decode k a n. Sorted and unsorted n are included. Legal PowerSeries substitutions at X, Y+XY and Y identify the three inverse factors. The middle coefficient is binom(-a0,q) choose(q,h). A finite antidiagonal reindexing retains both guards j+h<=n0 and q+l<=n1; terms outside the admissible fiber vanish by the binomial choose coefficient or by the unsorted chart branch."))), DescribeRole.Theorem))));
}
