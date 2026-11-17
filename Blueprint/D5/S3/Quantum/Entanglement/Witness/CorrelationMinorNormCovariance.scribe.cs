using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness;

internal sealed class CorrelationMinorNormCovarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual normalized separable covariance nuclear bound", H("Actual normalized separable covariance nuclear bound"), Blocks(
            Entry("weighted-centered-nuclear", "weighted_centered_nuclear", "weighted centered nuclear",
                "For arbitrary finite real Euclidean families of local squared norm at most one and nonnegative weights summing to one, the actual centered weighted-outer CFC nuclear norm is bounded by sqrt((1-norm(mean x)^2)(1-norm(mean y)^2)). Zero weights and centered vectors are included. This is the covariance estimate attributed to Zhang2008 and Gittsovich2008, not a new covariance theorem.", DescribeRole.Theorem),
            Entry("actual-covariance-nuclear", "actual_covariance_nuclear", "actual covariance nuclear",
                "For every actual separable complex state and complete trace-product-normalized local Hermitian bases, the actual covariance C-ab transpose uses precisely the coefficient means of the actual partial traces. Left retains Bob and Right Alice. The proof uses an arbitrary finite separable decomposition and actual Parseval/purity bounds. The spectral-tail/purity and actual D31 equality consumer are proved below in this same module.", DescribeRole.Theorem),
            Entry("correlation-tail-purity", "correlation_tail_purity", "correlation tail purity",
                "For arbitrary positive finite dimensions and every actual separable state, the actual descending singular tail through min(dA,dB) squared is bounded by sqrt((1-Tr(rhoA squared))(1-Tr(rhoB squared))). Coefficient means are the actual partial traces and Parseval supplies their actual purities. Dimension one and empty tails are included.", DescribeRole.Theorem),
            Entry("correlation-tail-corrected", "correlation_tail_corrected", "correlation tail corrected",
                "The purity upper bound is at most sqrt(((d-1)/d)((D-1)/D)), d=min(dA,dB), D=max(dA,dB), in arbitrary positive finite dimensions. This corrects the missing square root in printed D31, without validating Appendix D.5 extra maximization assumptions. Covariance credit remains Zhang et al. (2008), Theorem 1, and Gittsovich et al. (2008), Proposition IV.2.", DescribeRole.Theorem),
            Entry("d31-counterexample-and-equality", "d31_counterexample_and_equality", "d31 counterexample and equality",
                "The actual separable density omega(4,0) has both maximally mixed marginals, hence FNF. In every normalized complete Bob basis with normalized Pauli Alice basis, its complete singular tail is exactly sqrt(3/8), equal to the purity and dimension corrections and strictly larger than printed D31 value 3/8. This is an exact matrix and spectral proof, not a finite control.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/peledteenicarmicohen2021minor")),
            Blocks(Paragraph(Text(text))), role);
}
