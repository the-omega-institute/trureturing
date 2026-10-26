using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class ThreeFieldOriginalMiddleInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Supported middle reconstruction", H("Supported middle reconstruction"), Blocks(
            Describe.Lean(DescribeId.Create("original-middle-qslice-lower"),
                DeclarationHandle.Create(Prefix + "qSlice_lower"),
                H("qSlice_lower"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A fixed finite mode fiber supplies a uniform lower first-coordinate bound for its polynomial slice. The inverse shifts only the first and spectator coordinates, so this fiber is independent of the inverse length."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-middle-positiveclear-qslice"),
                DeclarationHandle.Create(Prefix + "positiveClear_qSlice"),
                H("positiveClear_qSlice"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positive clearing commutes with the two finite polynomial sums defining qSlice. The equality uses finite sum interchange and scalar commutation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-middle-middle-bounds"),
                DeclarationHandle.Create(Prefix + "middle_bounds"),
                H("middle_bounds"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nonnegative numerator coordinates imply j+l <= b+k, q <= s+2k+j and q+l <= s+b+3k, together with the three signed cone inequalities and the exact first-two-coordinate balance. No individual raw target exponent is required to be nonnegative."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-middle-mem-middlefiber-iff"),
                DeclarationHandle.Create(Prefix + "mem_middleFiber_iff"),
                H("mem_middleFiber_iff"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The containing finite box filtered by all three nonnegative numerator coordinates contains exactly every admissible triple. The box bounds follow from the signed balances, including all negative target branches."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-middle-middlesum-zero"),
                DeclarationHandle.Create(Prefix + "middleSum_zero"),
                H("middleSum_zero"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact finite sum vanishes when b+k, s+b+3k, or the total shifted exponent s+b+z+3k+a0+a1+a2 is negative."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-middle-middlecutoffsum-eq"),
                DeclarationHandle.Create(Prefix + "middleCutoffSum_eq"),
                H("middleCutoffSum_eq"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every auxiliary T at least k, the successive finite inverse sum equals the same exact middleFiber sum. Padding the j and q ranges contributes only zero native numerator coefficients. The negative b+T branch is included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-middle-qslice-partialclear"),
                DeclarationHandle.Create(Prefix + "qSlice_partialClear"),
                H("qSlice_partialClear"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full finite slice equals difference clearing of the partial positive clearing, with both original monomial shifts s^k and y^k retained."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-middle-original-middle-reconstruction"),
                DeclarationHandle.Create(Prefix + "original_middle_reconstruction"),
                H("original_middle_reconstruction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a commutative complex algebra, a raw family with a uniform lower second-coordinate bound and a derived short positive inverse is recovered by the exact finite middleFiber sum whenever its cleared numerator vanishes outside the native nonnegative octant. The short inverse is a premise of this general supplier; the actual canonical consumer proves it from descendant truncation. No finite-support assumption is imposed on the numerator. Supported difference and positive inversions are reused from SupportedChannelSeries, retaining Carnahan attribution. The chamber is b << s << z; no substitution is applied to an unrestricted raw distribution."))), DescribeRole.Theorem))));
}
