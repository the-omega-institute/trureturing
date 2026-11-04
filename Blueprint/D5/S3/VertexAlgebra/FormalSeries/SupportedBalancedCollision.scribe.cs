using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class SupportedBalancedCollisionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/SupportedBalancedCollision.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced native collision", H("Balanced native collision"), Blocks(
            Describe.Lean(DescribeId.Create("supportedbalancedcollision-balancedcross"),
                DeclarationHandle.Create(Prefix + "balancedCross"),
                H("The original cross factors"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite action of (y-z)^k(x-z)^k on the original labelled coefficients. The u/v factor is applied separately to recover the exact original clearing polynomial."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("supportedbalancedcollision-balancedarguments"),
                DeclarationHandle.Create(Prefix + "balancedArguments"),
                H("Legal positive coordinates"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native power-series substitution has arguments [s+x,x,z]. Its coordinates have zero constant coefficient, so it applies to a generally infinite numerator. Conjugation of the accepted outer collision by the label swap 1 and 2 gives the exact signed slice, including negative exponent zeros. This is a native-series substitution only."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("supportedbalancedcollision-balancedcollision"),
                DeclarationHandle.Create(Prefix + "balancedCollision"),
                H("The same infinite numerator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The output uses the original P under the lawful native [s+x,x,z] substitution. No new numerator is independently chosen."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("supportedbalancedcollision-balancedslice"),
                DeclarationHandle.Create(Prefix + "balancedSlice"),
                H("Fixed original third exponent"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("After swapping labels 1 and 2, middleNativeSlice fixes the original z exponent. Its bivariate variables are the original first and second coordinates. The collision gives the balanced [s,x,z] coefficient in precisely that order."))), DescribeRole.Definition))));
}
