using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class PhaseMemoryCompactDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/PhaseMemoryCompact.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attainment of finite-memory pure-state guessing optima.",
        H("Compactness of attainable memory scores"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-phase-memory-score-compact"),
                DeclarationHandle.Create(Module + "successSet_isCompact"),
                H("The unrestricted CPTP and POVM score set is compact"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For fixed finite input, memory and label sets, at most dim(input) times dim(memory) Kraus operators suffice to represent every CPTP encoder. Use an array of that size with zero padding and the completeness equation ΣₖKₖ†Kₖ = I. Its diagonal bounds all Kraus entries in the complex unit disk. The finite POVM tuples are closed with 0 ≤ Dⱼ ≤ I. The product of these compact sets maps continuously onto the full score set by the Born expression. The proof of compactness holds for arbitrary fixed vectors, including normalized signal vectors."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-phase-memory-score-maximum"),
                DeclarationHandle.Create(Module + "exists_isGreatest_successSet"),
                H("A nonempty memory and label set admit an optimal strategy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A reset channel and a deterministic guess give an attainable score when the memory and label sets are nonempty. Compactness then supplies a greatest score realized by one CPTP encoder and one POVM."))),
                DescribeRole.Theorem))));
}
