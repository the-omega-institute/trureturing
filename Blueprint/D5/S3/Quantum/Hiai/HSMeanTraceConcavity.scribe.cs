using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class HSMeanTraceConcavityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HSMeanTraceConcavity", H("HSMeanTraceConcavity"), Blocks(
            Describe.Lean(DescribeId.Create("meanProduct-triple-concave"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/HSMeanTraceConcavity.meanProduct_triple_concave"),
                H("Triple operator concavity"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("For p and theta in [0,1], form P_p(X,W)=L_(X^p) R_(W^(1-p)). Its joint operator concavity follows from the public full HS perspective identity and all-Hilbert power-perspective concavity. Mix A, B and W with one common coefficient. Both-input mean monotonicity compares the endpoint mixtures with the two Lieb lifts at the mixture; joint mean concavity then yields the triple operator inequality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gamma-triple-concave"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/HSMeanTraceConcavity.gamma_triple_concave"),
                H("Triple trace concavity"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("For arbitrary fixed Z, Gamma(A,B,W)=Re Tr(Z adjoint (B^p #theta A^p) Z W^(1-p)) is jointly concave in all three strictly positive inputs, for p and theta in [0,1]. The common-right-factor identity identifies the HS geometric mean. Evaluation at the fixed HS vector Z preserves the operator inequality. No positivity is asserted for the nonsymmetric product inside the trace, and Z may be singular or zero. This is the joint auxiliary-variable inequality required for endpoint-optimizer interpolation."))), DescribeRole.Theorem),
            Paragraph(Text("These are classical operator-mean and tracial variational arguments. The source dependencies retain their attribution and licenses. Full Hiai Problem 5.18 additionally requires inverse-geometric identification, its original parameter assembly and the support-preserving positive semidefinite extension. The native four-slot audit remains unfinished under issue #5214; no declared_validated registration is claimed.")))));
}
