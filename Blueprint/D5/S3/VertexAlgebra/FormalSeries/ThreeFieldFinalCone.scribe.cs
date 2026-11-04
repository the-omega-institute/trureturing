using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class ThreeFieldFinalConeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native chart and its unit", H("The native chart and its unit"), Blocks(
            Describe.Lean(DescribeId.Create("final-cone"),
                DeclarationHandle.Create(Prefix + "FinalCone"),
                H("FinalCone"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The three cumulative signed coordinates are nonnegative; no positivity of individual raw exponents is imposed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("decode"),
                DeclarationHandle.Create(Prefix + "decode"),
                H("decode"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every n in natural three-space, the signed raw exponent is (n0-k,n1-n0-2k,n2-n1-a0-a1-a2). No sortedness of n is required."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cone-equiv"),
                DeclarationHandle.Create(Prefix + "coneEquiv"),
                H("coneEquiv"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cumulative coordinates give a bijection from FinalCone to all natural three-space. Conversion to natural numbers occurs after proving nonnegativity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("old-zero-outside"),
                DeclarationHandle.Create(Prefix + "old_zero_outside"),
                H("old_zero_outside"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite Laurent expression vanishes outside FinalCone by its signed exponent balances."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-chart"),
                DeclarationHandle.Create(Prefix + "nativeChart"),
                H("nativeChart"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient at (r,s,t) is the numerator coefficient at (r,s-r,t-s) when r<=s<=t, and zero otherwise."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("old-coefficient-chart-sum"),
                DeclarationHandle.Create(Prefix + "old_coefficient_chart_sum"),
                H("old_coefficient_chart_sum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every decoded native index, the Laurent coefficient is the sum on its original finite fiber of the weights times the nativeChart coefficient at (n0-j-h,n1-q-l,n2)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-chart-factorization"),
                DeclarationHandle.Create(Prefix + "native_chart_factorization"),
                H("native_chart_factorization"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under x=XYZ,y=YZ,z=Z, the literal six factors x^k y^k (x+y)^k (x+y+z)^A (y+z)^C z^D factor as X^k Y^(3k) Z^(3k+A+C+D) times (1+X)^k (1+Y+XY)^A (1+Y)^C in every commutative ring."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("chart-unit-series"),
                DeclarationHandle.Create(Prefix + "chartUnitSeries"),
                H("chartUnitSeries"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The product (1+X)^k (1+Y+XY)^a0 (1+Y)^a1 has constant coefficient one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("chart-unit"),
                DeclarationHandle.Create(Prefix + "chartUnit"),
                H("chartUnit"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This series is a unit over any commutative ring, with inverse supplied by MvPowerSeries.invOfUnit."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("native-unit-equation"),
                DeclarationHandle.Create(Prefix + "native_unit_equation"),
                H("native_unit_equation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiplying the unit series by its inverse times nativeChart P returns nativeChart P for every formal series P."))), DescribeRole.Theorem))));
}
