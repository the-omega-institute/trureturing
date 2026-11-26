using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.ConditionalExpansion;

internal sealed class FilteredChannelConditionalGapDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap.";

    private static readonly LibraryNoteRef ConditionalExpansion =
        LibraryNoteRef.Create("D5/L/QuantumChannels/hirchegeorgenuradhawilde2026conditional");

    private static DocumentBlock.Describe Theorem(string name, string id, string title,
        params DocumentBlock[] description) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(ConditionalExpansion),
            Blocks(description), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite channel obtained by positive filtering has a uniform lower bound on conditional trace gaps.",
        H("Conditional trace-gap lower bound for filtered channels"),
        Blocks(
            Describe.Lean(DescribeId.Create("filtered-channel-action"),
                DeclarationHandle.Create(Prefix + "filterAction"),
                H("Filtered action"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite index types A and E, let e be the cardinality of E. "
                    + "Given G on A × E, the action sends each complex input matrix Z to "
                    + "√G ((Z ⊗ Iₑ)/e) √G."))), DescribeRole.Definition),
            Theorem("exists_filtered_channel", "filtered-channel-cptp", "Exact CPTP realization",
                Paragraph(Text("Suppose E is nonempty, G is positive definite, and the partial trace of G "
                    + "over E divided by e is I on A. There exists a finite quantum channel N from A to A × E "
                    + "whose action equals the filtered action on every complex input matrix. "
                    + "Its Kraus operators are √G times the environment basis injections, divided by √e. "
                    + "Their adjoint products sum to I by the partial trace normalization."))),
            Theorem("filtered_channel_conditional_trace_gap", "filtered-channel-hermitian-gap",
                "Hermitian gap under an inverse-marginal bound",
                Paragraph(Text("Assume the same positivity and normalization, and let N have the exact filtered "
                    + "action. Let L be the partial trace of G⁻¹ over E divided by e. If L ≤ kI in Loewner order "
                    + "for a real k > 0, the output conditional gap is at least 1/k times the input conditional gap. "
                    + "For a Hermitian joint input Z on R × A, the input gap is the trace of the negative part of Z "
                    + "minus that of its reference marginal. The output uses the amplified channel on Z and the "
                    + "same reference marginal. This holds for every finite R, including singular Z and "
                    + "mixed-sign reference marginals.")),
                Paragraph(Text("Lift the negative spectral projector of the reference marginal and take the "
                    + "normalized tensor extension by the environment identity. The derivative-free quadratic "
                    + "congruence bound applies with t = 1/k. Tracing out the environment bounds the inverse "
                    + "pairing by k times the input gap. Trace normalization preserves the reference projector term."))),
            Theorem("filtered_channel_norm_trace_gap", "filtered-channel-norm-gap", "Operator norm specialization",
                Paragraph(Text("When A is also nonempty, L is positive definite and is bounded above by its "
                    + "operator norm times I. The lower bound on the output gap therefore has factor 1/‖L‖ "
                    + "for every finite reference and every Hermitian Z under the same filter hypotheses."))),
            Theorem("filtered_channel_ratio_lower_bound", "filtered-channel-ratio-floor",
                "Lower bound on conditional hockey-stick ratios",
                Paragraph(Text("For nonempty A and E and the same positive, normalized filter, every admissible "
                    + "conditional hockey-stick ratio of N is at least 1/‖L‖. Apply the Hermitian bound to "
                    + "γσ − ρ and divide by the strictly positive input gap. This applies to every real γ "
                    + "and either choice of the orthogonality flag. At γ = 1, when admissible ratios exist, "
                    + "it bounds the conditional trace-distance expansion infimum in Definition 3, Eq. (2.42). "
                    + "Attainment and sharpness of the recovery comparison remain outside these results."))))));
}
