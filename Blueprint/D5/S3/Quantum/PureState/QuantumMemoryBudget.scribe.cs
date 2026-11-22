using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class QuantumMemoryBudgetDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/QuantumMemoryBudget.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite CPTP memory imposes a scalar budget on flat phase records.",
        H("The diagonal budget for decoding through quantum memory"),
        Blocks(
            Describe.Lean(DescribeId.Create("phase-memory-effect-family-minkowski"),
                DeclarationHandle.Create(Module + "sum_scores_le_of_effect_family"),
                H("An effect family is bounded by its summed diagonal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each positive effect, take its positive matrix square root and apply the Euclidean triangle inequality over carrier coordinates to the square root acting on the signal. The norm of each column is the square root of the corresponding effect diagonal. A second Euclidean triangle inequality, this time over labels, bounds the sum of scores by the square of the amplitude sum weighted by √dᵢ, where dᵢ is the sum of the effect diagonals at coordinate i."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("phase-memory-universal-profile-bound"),
                DeclarationHandle.Create(Module + "exists_success_le_profile"),
                H("Every common CPTP encoder and output POVM yields a feasible profile"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consider normalized finite signals with the same nonnegative amplitudes t and unit-modulus phases for each label. Pull back each output POVM effect and use the spectral supplier's score-preserving compression. The compressed effects sum to at most the identity, and each trace is bounded by the corresponding output effect trace. Their summed diagonal has entries in [0,1] and total mass at most the memory dimension M. For uniform labels, the success is at most the square of the profile value divided by the number of labels. This upper bound only requires unit-modulus phases."))),
                DescribeRole.Theorem))));
}
