using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class ForwardTraceYoungDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ForwardTraceYoung", H("ForwardTraceYoung"), Blocks(
            Describe.Lean(DescribeId.Create("forward-trace-young"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/ForwardTraceYoung.forward_trace_young"),
                H("Forward tracial Young inequality"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/carlenlieb2008minkowski")),
                Blocks(Paragraph(Text("For all finite complex matrix dimensions, positive definite M and W and 0<p<=1, Re Tr(M W^(1-p))-(1-p) Re Tr W <= p Re Tr(M^(1/p)). For 0<p<1, apply the existing Schatten Holder supplier to M^(1/2) W^((1-p)/2) at exponents 2, 2/p and 2/(1-p). The public column-Gram identity and trace cyclicity give the mixed trace. Raising the bound to two and applying scalar weighted Young proves the result. The endpoint p=1 is calculated separately. Empty dimension and noncommuting M,W are retained."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("maximum-and-attainment"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/ForwardTraceYoung.maximum_and_attainment"),
                H("Explicit attained maximum"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/carlenlieb2008minkowski")),
                Blocks(Paragraph(Text("The positive definite optimizer is exactly W0=M^(1/p), and the objective equals p Re Tr(M^(1/p)) there and dominates its value at every positive definite W. The equality uses same-matrix spectral power arithmetic. No positive definite optimizer is asserted for singular M. The mean-trace concavity proof interpolates the two actual endpoint optimizers; it needs joint concavity in the auxiliary variable, not a supremum of separately concave functions."))), DescribeRole.Theorem),
            Paragraph(Text("These are classical operator-mean and tracial variational arguments. The source dependencies retain their attribution and licenses. Full Hiai Problem 5.18 additionally requires inverse-geometric identification, its original parameter assembly and the support-preserving positive semidefinite extension. The native four-slot audit remains unfinished under issue #5214; no declared_validated registration is claimed.")))));
}
