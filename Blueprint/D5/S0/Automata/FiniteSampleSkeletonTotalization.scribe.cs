using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class FiniteSampleSkeletonTotalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Automata/FiniteSampleSkeletonTotalization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First-return skeletons admit successful-run-preserving totalization and exact-behavior recurrent capacity padding, with explicit used-signature costs.",
        H("Finite Sample Skeleton Totalization and Capacity Padding"),
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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("total-signature-pair-cost"),
                DeclarationHandle.Create(Prefix + "total_canonical_cost_eq_pair_cost"),
                H("Total signature cost is ordinary output-return pair cost"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Totality makes every used optional return target present. Removing this wrapper gives an equivalence with used ordinary output-return pairs and preserves cardinality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signature-source-count-bound"),
                DeclarationHandle.Create(Prefix + "signature_card_le_recurrent_card"),
                H("At most one used signature per recurrent source"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Determinism makes the choice of one recurrent source per used signature injective. This gives the source-count constraint used by the capacity search."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("capacity-padding-option-evaluation"),
                DeclarationHandle.Create(Prefix + "eval_padSkeleton"),
                H("Capacity padding preserves defined and undefined evaluations"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The state carrier is the sum of the original carrier and extra capacity. Each extra state emulates the original start, while all transition targets remain in the original summand. Evaluation from any padded state agrees with evaluation from its collapsed original state, including none results."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("capacity-padding-signature-surjection"),
                DeclarationHandle.Create(Prefix + "paddingSignatureMap_surjective"),
                H("Extra recurrent states request no new signature"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A padded state's signature request is the embedded request of its collapsed original source. Thus every used padded signature has an original preimage. Together with injectivity of embedded return targets, this yields an exact bijection of used signatures."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("capacity-padding-exact-signature-cost"),
                DeclarationHandle.Create(Prefix + "pad_signature_card_eq"),
                H("Used signature cardinality is exactly unchanged"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Capacity padding neither merges nor adds used signatures. This theorem permits an empty original signature set because padding does not fill undefined transitions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("capacity-padding-totality"),
                DeclarationHandle.Create(Prefix + "pad_isTotal"),
                H("Padding preserves totality"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When every original transition and return is defined, each added start-state copy is total as well. A separate companion preserves the start-zero-loop, and the start output is unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("capacity-padding-canonical-cardinality"),
                DeclarationHandle.Create(Prefix + "pad_canonical_state_card"),
                H("Canonical state cost increases only by allocated recurrent capacity"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The signature cost is identical, while the recurrent carrier gains exactly the chosen number of extra states. Padding does not claim that total state cost itself remains unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-capacity-padding-existence"),
                DeclarationHandle.Create(Prefix + "exists_fixed_capacity_padding"),
                H("Represent the same behavior at any larger recurrent capacity"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The construction allocates the finite capacity difference, preserves all block-code evaluations and exact used-signature cost, and transports totality when supplied. This is intended for the M19.3 weighted fixed-capacity consumer. It permits unused states; it does not justify an encoding requiring every allocated state to be reachable."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("conditional-fourteen-capacity-cover"),
                DeclarationHandle.Create(Prefix + "budget_fourteen_capacity_cover"),
                H("Conditional arithmetic coverage of the fourteen-state budget"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Given a total budget of fourteen, the source-count bound, and a separately proved signature lower bound of three, five capacity rectangles suffice. This companion proves only arithmetic coverage. It supplies neither the sample-specific lower bound of three nor any UNSAT certificate."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Automata/BinaryZeckendorfBlockSkeleton")),
        ]));
}
