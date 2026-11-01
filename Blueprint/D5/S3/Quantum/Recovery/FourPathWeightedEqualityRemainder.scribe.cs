using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class FourPathWeightedEqualityRemainderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a four-dimensional unitary transport matrix, the Hilbert--Schmidt distance to a phased nonnegative diagonal is controlled by the squared trace defect.",
        H("Four-path weighted equality remainder"),
        Blocks(Describe.Lean(
            DescribeId.Create("four-path-weighted-equality-remainder"),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathWeightedEqualityRemainder.weighted_equality_remainder"),
            H("Weighted equality remainder"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For v : C^4 and U in U(4), let K = U diag(v), L be the sum of coordinate moduli, t be the trace modulus, and tau = L squared minus t squared. A unit phase lambda satisfies the Hilbert--Schmidt bound ‖K - lambda diag(|v|)‖ squared <= 2 tau.")),
                Paragraph(Text("The phase aligns the trace. Unitary entry bounds make the coordinate residuals nonnegative; the Frobenius expansion gives the weighted residual sum, and the trace triangle inequality supplies the final factorization."))),
            DescribeRole.Theorem))));
}
