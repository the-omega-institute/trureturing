using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class SparseEndpointTailModulusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/SparseEndpointTailModulus.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Selective annihilation gives a one-sided endpoint certificate with an explicit positive-tail charge.",
        H("Sparse Endpoint Tail Modulus"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sparse-endpoint-tail-modulus-content"),
                DeclarationHandle.Create(Prefix + "sparse_endpoint_tail_modulus"),
                H("Separation-free retained-endpoint bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual Prony moments of n retained nonnegative atoms and an arbitrary finite positive residual are compared with a positive finite spectrum below b. An atom of retained weight at least eta above b forces eta times its endpoint displacement to the power 2n-1 to be at most 2^(2n-1) epsilon plus the residual mass budget. The proof constructs a selective sign annihilator, propagates moment errors by factor induction, and proves the unit-norm tail charge. Neither spectral separation nor distinct nodes nor normalization is assumed. The comparator mode count is unrestricted. Sparse-moment stability is classical background; the displayed asymmetric tail-aware estimate is the precise application result. No unbounded-operator or physical Yang-Mills identification is asserted."))),
                DescribeRole.Theorem))));
}
