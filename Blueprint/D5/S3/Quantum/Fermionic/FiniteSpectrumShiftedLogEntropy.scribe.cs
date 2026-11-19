using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class FiniteSpectrumShiftedLogEntropyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/FiniteSpectrumShiftedLogEntropy.";
    private const string Digest = "Finite-spectrum entropy order from actual shifted determinant order.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Digest, H("Entropy comparison from shifted products"), Blocks(
            Entry("integral_log_shifted_product_sub_eq", "The logarithmic integral at finite cutoff",
                "Two nonnegative spectra on the same finite index type and with equal sums have matching constant and linear cutoff terms. The integral of the difference of the logarithms of their shifted products is the entropy difference plus a difference of remainders."),
            Entry("entropy_le_of_shifted_product_le", "Shifted product order implies entropy order",
                "If one shifted product is larger at every positive shift, its spectrum has greater or equal entropy. The remainder for an entry x is bounded by its square divided by the cutoff. A zero entry contributes zero entropy."),
            Entry("bravyi_three_mode_entropy_ge_comparator", "Entropy order for the real Bravyi blocks",
                "Apply the finite-spectrum comparison to the chiral and complementary matrices using the orders of their shifted determinants. The complementary block contributes twice to the resulting inequality."))));

    private static DocumentBlock Entry(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("shifted-log-entropy-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
