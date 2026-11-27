using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BravyiThreeModePhysicalEntropyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/BravyiThreeModePhysicalEntropy.";
    private const string Digest = "Physical output entropy of the three-mode Bravyi channel on its normal form.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Digest, H("Physical output entropy on the three-mode normal form"), Blocks(
            Paragraph(Text("The input is the rank-one projector of a normalized real chiral spinor. "
                + "The channel is a trace-preserving sum of Clifford conjugations with nonnegative weights "
                + "throughout the closed attenuation interval.")),
            Entry("normalOutput_spectrum", "The complete output spectrum",
                "The physical output is complex Hermitian. Under the signed basis change its characteristic polynomial factors into that of the real chiral block and those of the two complementary blocks. Its roots give the multiset of all eight eigenvalues with their algebraic multiplicities."),
            Entry("normalOutput_entropy_eq_blocks", "The physical entropy as a block sum",
                "Apply the von Neumann spectral entropy formula to the density state. The complementary entropy is counted twice, and every zero eigenvalue contributes zero."),
            Describe.Lean(DescribeId.Create("shifted-log-entropy-bravyi-three-mode-entropy-ge-comparator"),
                DeclarationHandle.Create(Prefix + "bravyi_three_mode_entropy_ge_comparator"),
                H("Entropy order for the real Bravyi blocks"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The comparator determinant formulas give strict positivity at every positive shift, including at the endpoints of the attenuation interval. "
                    + "The determinant differences also give equal traces on the two sides of each comparison. Applying the shifted-product theorem to the two block spectra counts the complementary block twice."))), DescribeRole.Theorem),
            Entry("comparator_entropy_le_normalOutput", "The physical comparator has minimum entropy",
                "For every real unit normal-form spinor and every attenuation from zero through one, the output entropy is at least the output entropy at the comparator spinor. "
                + "Its first and third amplitudes are the positive square root of one half and its second amplitude is zero. "
                + "The shifted determinant ordering bounds the chiral and complementary entropy contributions separately. The spectrum formula then adds the complementary contribution twice."))));

    private static DocumentBlock Entry(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("bravyi-physical-entropy-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
