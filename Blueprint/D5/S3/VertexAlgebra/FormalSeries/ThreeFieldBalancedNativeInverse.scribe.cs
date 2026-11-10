using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class ThreeFieldBalancedNativeInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedNativeInverse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native constant-one unit", H("The native constant-one unit"), Blocks(
            Describe.Lean(DescribeId.Create("threefieldbalancednativeinverse-balancedunitseries"),
                DeclarationHandle.Create(Prefix + "balancedUnitSeries"),
                H("The native constant-one unit"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For S=s/z and T=z/x in the native cumulative chart, the unit is (1+ST)^a0 (1+ST-T)^k (1-T)^k. Only native power series are substituted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("threefieldbalancednativeinverse-rawbalancedcoefficient"),
                DeclarationHandle.Create(Prefix + "rawBalancedCoefficient"),
                H("Signed native coefficients"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse unit times the reordered native numerator is read at (s+k,s+z+k+a2,s+z+x+a0+a1+a2+3k), with zero extension at every negative native coordinate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("threefieldbalancednativeinverse-raw-balanced-action"),
                DeclarationHandle.Create(Prefix + "raw_balanced_action"),
                H("Exact literal clearing action"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite monomial translations and native unit cancellation recover the original signed numerator under the literal balanced polynomial for every signed target and every generally infinite numerator."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("threefieldbalancednativeinverse-raw-balanced-support"),
                DeclarationHandle.Create(Prefix + "raw_balanced_support"),
                H("Support of the inverse"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse expression has the uniform s cutoff -k and, at each fixed s, the z cutoff -(s+k+a2). No x bound is asserted."))), DescribeRole.Theorem))));
}
