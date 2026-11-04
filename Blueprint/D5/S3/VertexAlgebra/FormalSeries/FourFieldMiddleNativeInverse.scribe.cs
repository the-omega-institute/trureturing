using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class FourFieldMiddleNativeInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleNativeInverse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("FourFieldMiddleNativeInverse", H("FourFieldMiddleNativeInverse"), Blocks(
            Describe.Lean(DescribeId.Create("fourfieldmiddlenativeinverse-numeratorslice"), DeclarationHandle.Create(Prefix + "numeratorSlice"),
                H("Native numerator slices"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A generally infinite native four-variable numerator is read into three native cumulative indices, with its fourth total degree kept as a signed parameter. The signed outer numerator coordinate and both unsorted branches are retained."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fourfieldmiddlenativeinverse-middleunitseries"), DeclarationHandle.Create(Prefix + "middleUnitSeries"),
                H("The constant-one middle unit"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With b=STU,y=TU,z=U and outer coordinate one on each total-degree slice, the unit is (1+ST)^a1 (1+ST-T)^k (1-T)^k (1-U-STU)^k (1-U)^k (1-TU)^k. Its constant coefficient is one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fourfieldmiddlenativeinverse-rawmiddlecoefficient"), DeclarationHandle.Create(Prefix + "rawMiddleCoefficient"),
                H("Native inverse coefficients"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse unit multiplies the native numerator slice at total x+b+z+y+sum(a)+6k and is read at b+k,b+y+k+a3,b+y+z+a1+a2+a3+3k. This constructs native series without substituting any unrestricted raw distribution."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fourfieldmiddlenativeinverse-raw-middle-action"), DeclarationHandle.Create(Prefix + "raw_middle_action"),
                H("Actual finite polynomial action"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite variable translations with their total-degree shifts prove that the literal Rmid action on this native inverse recovers the original signed numerator at every four-index target."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourfieldmiddlenativeinverse-raw-middle-support"), DeclarationHandle.Create(Prefix + "raw_middle_support"),
                H("Derived native support"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Native nonnegativity gives nested b,y,z cutoffs. These bounds are properties of the inverse; the actual channel may have arbitrary different nested bounds."))), DescribeRole.Theorem))));
}
