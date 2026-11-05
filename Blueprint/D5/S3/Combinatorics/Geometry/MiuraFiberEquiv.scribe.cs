using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraFiberEquivDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraFiberEquiv.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The whole actual fixed-core fiber is a product of positive vectors.", H("The whole actual fixed-core fiber is a product of positive vectors"),
        Blocks(
            Describe.Lean(DescribeId.Create("miurafiberequiv-0"),
                DeclarationHandle.Create(Prefix + "core_positive_vectors_equiv"), H("An equivalence of the original actual fiber"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every existing Core(a,b) member K and every rectangle m,n at least 2(a+b)-1, the product PositiveLengths(m-rowOccupied K,rowRuns K) times PositiveLengths(n-colOccupied K,colRuns K) is equivalent to the entire actual residual fiber reducing to K. The fiber retains the exact integer-valued normalized function and, for each physical side separately, equivalence of the assertion that all minima lie on that side. The inverse reads supported weights along an actual reduction and adds the compulsory first line of each isolated frozen run. Equal positive readouts imply equal weights, then equality of every actual height value. Conversely, the existing simultaneous indexed realization produces an actual residual function for every positive vector; exact occupied-position uniqueness reads back that same vector. The equivalence therefore includes all individual functions in the stated fiber."))), DescribeRole.Theorem))));
}
