using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class HilbertSchmidtTraceStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hilbert-Schmidt square-root error controls trace error.",
        H("Hilbert-Schmidt square-root error controls trace error"), Blocks(
            Describe.Lean(
                DescribeId.Create("entrynormsq-eq-hs-sq"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/HilbertSchmidtTraceStability.entryNormSq_eq_hs_sq"),
                H("Entry squares are the Frobenius norm squared"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite square complex matrix A, entryNormSq(A) = sum_i sum_j |A_ij|^2 = ||A||_HS^2. The norm is explicitly the Frobenius norm, not an operator or entrywise supremum norm. This normalization is consumed by the full spectral Parseval step in PetzPhysicalWeightedCoordinates.physical_weighted_parseval. It is a repository norm identity, not a separate novelty claim."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tracenorm-sub-le-four-hs-sqrt"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/HilbertSchmidtTraceStability.traceNorm_sub_le_four_hs_sqrt"),
                H("A normalized positive Gram majorant gives a trace bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let R be positive semidefinite with Tr(R)=1, let Tr(N)=1, and suppose C C* <= N in the positive-semidefinite order. Then ||N-R||_1 <= 4 ||C-sqrt(R)||_HS. No invertibility or commutativity is assumed; N is positive because it majorizes C C*. Writing delta=||C-sqrt(R)||_HS, the positive remainder N-C C* has trace norm at most 2 delta, and the product expansion bounds ||C C*-R||_1 by 2 delta. PetzCoreTraceStability.petz_core_traceNorm_le_four_physical_hs consumes this estimate with C=H Psi(Y) P_R. This auxiliary estimate is retained for that proof path and makes no literature novelty claim."))),
                DescribeRole.Theorem))));
}
