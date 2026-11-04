using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class SupportedFourFieldMiddleInjectivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldMiddleInjectivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("SupportedFourFieldMiddleInjectivity", H("SupportedFourFieldMiddleInjectivity"), Blocks(
            Describe.Lean(DescribeId.Create("supportedfourfieldmiddleinjectivity-middlesupport"), DeclarationHandle.Create(Prefix + "MiddleSupport"),
                H("Actual nested support"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The signed coefficient order is x,b,z,y. There is a global b lower bound, a y lower bound at each b, and a z lower bound at each b,y, all uniform in outer x. The nested bounds may depend arbitrarily on the preceding exponents."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("supportedfourfieldmiddleinjectivity-middle-injective"), DeclarationHandle.Create(Prefix + "middle_injective"),
                H("Literal middle cancellation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact ten-factor Rmid is injective on this nested support. Fixed-y slices reuse the three-field triple difference and x-z kernels; fixed-z slices reuse the three-field x-y difference kernel. The balanced core is cancelled at each fixed outer x by the three-field balanced injectivity theorem. Finite Laurent translations preserve the necessary support; no fixed global cone is assumed."))), DescribeRole.Theorem))));
}
