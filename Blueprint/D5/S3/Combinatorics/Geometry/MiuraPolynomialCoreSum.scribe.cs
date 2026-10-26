using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraPolynomialCoreSumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite rational candidate from individual residual cores.", H("The actual-core run-vector polynomial"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuracoresum-0"),
                DeclarationHandle.Create(Prefix + "CoreState"), H("An individual residual core"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each state is a normalized height function with the exact specified minimum and maximum counts, the common physical-side exclusion, at least two cells per axis, no adjacent frozen pair on either axis, and at least one frozen run on each axis."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracoresum-1"),
                DeclarationHandle.Create(Prefix + "Core"), H("The finite family retains every actual core"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Dimensions are natural values below 2(a+b). The dependent family includes every individual core function at those dimensions. Finiteness follows from the finite normalized residual classes on each bounded rectangle."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracoresum-2"),
                DeclarationHandle.Create(Prefix + "rowOccupied"), H("Occupied rows"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Count actual rows containing at least one strict minimum or maximum by applying occupied-column counting to the transpose."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracoresum-3"),
                DeclarationHandle.Create(Prefix + "colOccupied"), H("Occupied columns"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Count actual columns containing at least one strict minimum or maximum."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracoresum-4"),
                DeclarationHandle.Create(Prefix + "rowRuns"), H("Actual frozen row runs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Count maximal frozen runs on the transposed column axis."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracoresum-5"),
                DeclarationHandle.Create(Prefix + "colRuns"), H("Actual frozen column runs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Count maximal frozen runs on the column axis."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracoresum-6"),
                DeclarationHandle.Create(Prefix + "corePolynomial"), H("One finite rational polynomial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Sum the two-variable positive-run polynomial over the finite family of individual actual residual cores. The sum is independent of the later evaluation dimensions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracoresum-7"),
                DeclarationHandle.Create(Prefix + "core_polynomial_eval"), H("Exact evaluation of the core-indexed vector sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For both dimensions at least 2(a+b)-1, evaluation equals the finite sum, over every individual core, of the cardinalities of its positive row-run and column-run vector products. Each total is the corresponding dimension minus the actual occupied-line count. The occupied-line and frozen-run bounds on each actual core prove that all positive-vector parameters are feasible throughout this region. Equality of this vector sum with the residual height-function count requires a canonical-core and expansion-fiber bijection."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracoresum-8"),
                DeclarationHandle.Create(Prefix + "core_polynomial_degree_le"), H("The strict total degree bound on these same actual cores"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a+b at least five, the total degree of this same core polynomial is at most a+b-3. The active-column run definitions are identified with the actual geometric row-run starts after transposition. Positive runs give an unoccupied row on each axis, so the strict residual geometry bound applies to every member of the existing Core family. Each summand has degree at most its two run counts minus two; the finite sum preserves the uniform bound. Equality of its evaluations with residualCount still requires the actual reconstruction and counting bridge."))), DescribeRole.Theorem))));
}
