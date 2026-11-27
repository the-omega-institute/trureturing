using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class JointRecordDecodingCrossoverDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/JointRecordDecodingCrossover.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attaining joint POVMs realize the finite-scale limit on the original carriers.",
        H("Finite-scale crossover of joint binary-record decoding"),
        Blocks(
            Describe.Lean(DescribeId.Create("product-record-optimum-crossover"),
                DeclarationHandle.Create(Module + "pGuess_productRecord_crossover"),
                H("The optimum for guessing the full word tends to exp(−scale / 4)"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At each index n, the carrier is finite and may depend on n. The pair of complex amplitudes each has squared norm one. With k_n independent fair bits and squared overlap x_n, assume x_n tends to zero, is eventually nonzero, and k_n x_n tends to the finite real scale. The optimal full-word success on the original product carrier tends to exp(−scale / 4)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("product-record-povm-crossover"),
                DeclarationHandle.Create(Module + "productRecordPOVM_crossover"),
                H("An attaining family and an upper bound uniform over competing POVMs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same hypotheses there is a family of joint POVMs on the original product carriers with success equal to the optimum at every index. Its success converges to exp(−scale / 4). For each positive tolerance, all POVMs at sufficiently large indices have success strictly below the limit plus that tolerance."))),
                DescribeRole.Theorem))));
}
