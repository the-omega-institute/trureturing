using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class FiniteSampleSkeletonTotalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Automata/FiniteSampleSkeletonTotalization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A used transient signature permits totalization of a first-return skeleton while preserving successful observations and not increasing canonical state cost.",
        H("Finite Sample Skeleton Totalization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("skeleton-totalization-success-and-cost"),
                DeclarationHandle.Create(Prefix + "totalization_preserves_success_and_cost"),
                H("Total extension with no greater canonical state cost"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The construction reuses the M17 Skeleton carrier. Missing zero transitions return to the original start state. Each old signature receives one uniform completed return target, and missing one channels reuse a supplied old signature.")),
                    Paragraph(Text("The start state and recurrent outputs are retained. Every successful original code evaluation is retained. Undefined runs may become defined, so equality of partial behaviors is not asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completion-signature-surjection"),
                DeclarationHandle.Create(Prefix + "completionMap_surjective"),
                H("Completed signatures are images of old used signatures"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicit surjection proves that completion can merge signature classes but cannot create a new class. The old-signature seed supplies the preimage for a previously absent one channel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("totalization-zero-loop"),
                DeclarationHandle.Create(Prefix + "totalize_preserves_zero_loop"),
                H("The start-zero-loop anchor is preserved"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An already defined start-state zero self-loop survives the completion. The separate recurrent-output equality preserves the published zero-output anchor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("transient-observation-supplies-seed"),
                DeclarationHandle.Create(Prefix + "signature_nonempty_of_transient_success"),
                H("A successful terminal-one observation supplies a seed"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The nonempty-signature premise can be derived from sample data containing a successful transient-channel observation. It is not assumed for an arbitrary empty-observation problem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-signature-totalization-obstruction"),
                DeclarationHandle.Create(Prefix + "empty_signature_cost_obstruction"),
                H("An empty signature set prevents zero-cost totalization"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A total skeleton has a defined one channel at its start state and therefore has at least one used transient signature. An original signature count of zero cannot be preserved."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sample-total-realization"),
                DeclarationHandle.Create(Prefix + "exists_total_sample_realization"),
                H("Transport a fitted sample family to a total realization"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One successful transient observation suffices for the construction. All labels in the supplied family remain correct, on the same recurrent carrier and at no greater canonical state cost. No CNF, SAT refutation, or numerical DFAO lower bound is claimed here."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Automata/BinaryZeckendorfBlockSkeleton")),
        ]));
}
