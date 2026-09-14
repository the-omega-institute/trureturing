using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.WeightedCapacity;

internal sealed class ProbeTopologySequencesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Convergent Sequences of Finite Capacity States.",
        H("Convergent Sequences of Finite Capacity States"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("probetopologysequences-tendsto-iff-eventually-eq"),
                DeclarationHandle.Create("D5/S3/Analytic/WeightedCapacity/ProbeTopologySequences.tendsto_tauPlus_iff_eventually_eq"),
                H("Convergence is eventual equality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each coordinate has a finite natural capacity, and every state has finite support. "
                    + "Equip these states with the initial topology of their golden coordinate phases "
                    + "and all circle characters defined by total rational coefficient sequences. "
                    + "A sequence converges to a state exactly when it eventually equals that state. "
                    + "No bound on the number of active coordinates or on total weighted capacity is needed. "
                    + "Single coordinate characters force each coordinate to stabilize. If unequal terms "
                    + "persist, their signed differences admit a subsequence with separated finite supports. "
                    + "One rational coefficient sequence then evaluates to one half on every selected "
                    + "difference, contradicting convergence of its circle character."))),
                DescribeRole.Theorem))));
}
