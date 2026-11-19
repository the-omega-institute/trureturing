using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class AuricOriginalInstrumentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/AuricOriginalInstrument.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact unhalved diamond error for the five-level flagged AURIC instrument.",
        H("Five-level flagged projective simulation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("original-instrument"),
                DeclarationHandle.Create(Prefix + "originalInstrument"),
                H("The full input channel with its terminal flag"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two zero-angle Kraus matrices in the source basis are combined with "
                    + "coefficients cos θ and i sin θ. Each Kraus term records its own flag and "
                    + "retains the five-level quantum output."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-instrument-eq-transport"),
                DeclarationHandle.Create(Prefix + "originalInstrument_eq_transport"),
                H("Unitary reduction at each real angle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A unitary on the full input register combines the angle rotation with "
                    + "the change of basis. A unitary on the same output register is selected "
                    + "by the terminal flag. Together these transform the diagonal two-branch "
                    + "target into the actual AURIC instrument on every complex input."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-exact-distance"),
                DeclarationHandle.Create(Prefix + "original_exact_distance"),
                H("Optimal error attained for every real angle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A root of the matching equation on the witness interval gives one "
                        + "common optimal error for all angles. A finite input-independent "
                        + "mixture of projective protocols attains the least uniform "
                        + "amplified trace-norm bound over the diamond closure. The bound "
                        + "tests arbitrary complex inputs with every finite passive reference.")),
                    Paragraph(Text(
                        "For the lower bound a fixed normalized purification tests the two "
                        + "flag blocks. After a nontrivial first projection, complementary "
                        + "ranks reduce to the rank-one and rank-two estimates. For the upper "
                        + "bound the explicit phase and permutation average of tilted "
                        + "one-measurement protocols has a completely positive Choi majorant. "
                        + "The matching equation gives the same bound as the witness."))),
                DescribeRole.Theorem))));
}
