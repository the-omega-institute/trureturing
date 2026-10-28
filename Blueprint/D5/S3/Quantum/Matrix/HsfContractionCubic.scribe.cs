using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfContractionCubicDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfContractionCubic";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full contraction cubic trace certificate",
        Blocks(
            Entry("coefficient_gap_identity", "Exact full contraction identity",
                "For arbitrary finite complex matrices A,B,K that are Hermitian, 144 times (2 coefficient2(A+B,A,K) minus 6 coefficient3(A+B,A,K)) equals the sum of four weighted traceGram forms with weights (A,I-K),(A,K),(B,I-K),(B,K) and matrices M00,M01,M10,M11. The eight words are Q,QK,CA,CAK,KCA,CB,CBK,KCB, where Q=A-(A+B)K, CA=AK-KA, CB=BK-KB. Each trace has exact order L (q_i)* R q_j. Only cyclic rotations identify words; no word reversal, projection relation or commutativity is assumed."),
            Entry("coefficient_gap_nonneg", "Positive-direction coefficient inequality",
                "For arbitrary finite complex U,H,K, assume H,U-H,K,I-K are PSD, including singular endpoints. Then 6 coefficient3(U,H,K) is at most 2 coefficient2(U,H,K). These are the original ordered coefficients of the actual exponent minus two thirds trace expansion. The statement is a coefficient result; actual derivatives and the signed constant-five conclusion require the separate analytic bridge."))));
    private static DocumentBlock Entry(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("hsfcontractioncubic-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
