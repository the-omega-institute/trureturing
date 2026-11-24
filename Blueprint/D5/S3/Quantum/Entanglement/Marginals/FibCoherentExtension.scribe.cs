using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class FibCoherentExtensionDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.coherent_extendible_iff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common-state criterion for two adjacent Fibonacci marginals with arbitrary coherences.",
        H("Coherent Fibonacci marginal extensions"),
        Blocks(
            Describe.Lean(DescribeId.Create("fib-coherent-extension"),
                DeclarationHandle.Create(Result), H("The residual endpoint marginals"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The five legal Fibonacci words split into the middle singleton and the "
                    + "four occupation patterns of the two endpoints. Let b be the weight of "
                    + "the singleton and let L and R be the two observed endpoint blocks, obtained "
                    + "by restricting each edge matrix to the empty-middle subspace. Both edges "
                    + "supply the same middle-to-vacuum entry. Each edge supplies one additional "
                    + "middle-to-endpoint entry. The middle-to-double-occupation entry is free.")),
                    Paragraph(Text(
                    "A common positive semidefinite trace-one state exists exactly when b is "
                    + "nonnegative, the two endpoint block traces both equal 1 - b, and there "
                    + "is a choice of the free entry for which both residual blocks are "
                    + "positive semidefinite and the entire coupling row vanishes if b = 0. "
                    + "For positive b the residuals subtract the "
                    + "respective endpoint marginals of the outer product of the conjugated "
                    + "middle row divided by b. At b = 0 the endpoint blocks themselves "
                    + "are the residuals.")),
                    Paragraph(Text(
                    "The scalar Schur complement gives the necessity of the residual conditions. "
                    + "Their traces agree by trace preservation. If their trace is positive, "
                    + "their tensor product divided by that trace gives a joint positive "
                    + "residual on the endpoints. At trace zero the residual blocks are zero. "
                    + "Restoring the outer product contribution and the middle singleton "
                    + "gives the required common state."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-coherent-pure"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.pure_coherent_iff"),
                H("Pure extensions at a prescribed coupling"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix the free coupling z and suppose the middle occupation b is nonzero. "
                    + "A pure trace-one extension exists exactly when the left endpoint block "
                    + "has trace one minus b and both Schur residuals at z are zero. In that case "
                    + "the pure density is the only positive semidefinite extension with the "
                    + "specified marginals and coupling.")),
                    Paragraph(Text(
                    "The middle amplitude x has squared modulus b and the middle row is x "
                    + "times the conjugate of the endpoint amplitudes. The endpoint block is "
                    + "therefore the outer product of the conjugated row divided by b. The "
                    + "trace condition and the left residual equation force b to be positive "
                    + "because for negative b the correction has nonpositive trace. Take x "
                    + "to be the positive square root of b and reconstruct the endpoint "
                    + "amplitudes from the row. Any positive extension with the same data has "
                    + "a positive semidefinite Schur residual with trace zero, so its endpoint "
                    + "block equals the same correction.")),
                    Paragraph(Text(
                    "At zero middle occupation, an endpoint-only pure state can have "
                    + "nonzero endpoint blocks. For example, the pure vacuum has two vacuum "
                    + "projections as endpoint blocks. The positive-pivot formula divides "
                    + "by b and requires the separate zero-occupation analysis."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-rational-prescribed-extension"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.rational_extension_at"),
                H("Rational extension at a prescribed coupling"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix a nonnegative middle occupation, rational observed entries, and a rational value for the unobserved coupling. Suppose the traces normalize the data, both residual marginals are positive semidefinite, and the row vanishes when the middle occupation is zero. The data admit a positive trace-one extension with rational real and imaginary parts in every entry.")),
                    Paragraph(Text("Normalization makes the middle occupation rational. Take the tensor product of the two residual blocks divided by their common trace. At trace zero both blocks vanish and the product contribution is zero. Restore the correction and the middle row. Each entry uses sums, products, conjugation and reciprocals of complex numbers with rational coordinates."))),
                DescribeRole.Theorem))));
}
