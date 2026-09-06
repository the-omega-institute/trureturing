using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class PublishedGoldenDFAStateLowerBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A one-way finite-prefix encoding and kernel-checked refutation exclude globally correct published golden base-four DFAOs in the same state budget.",
        H("Published Golden DFAO State Lower Bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("published-global-exclusion-from-prefix-refutation"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/PublishedGoldenDFAStateLowerBound.no_global_model_at_most_of_prefix_refutation"),
                H("A finite-prefix refutation gives a published global lower bound"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Global published correctness implies finite-prefix fitting. The one-way encoding maps every such finite model to a satisfying valuation, and the checked refutation excludes all valuations, yielding a global bounded-state exclusion within the same published machine class."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("published-twenty-two-state-minimality-target"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/PublishedGoldenDFAStateLowerBound.published_base4_twenty_two_state_minimality"),
                H("A verified upper machine and a 21-state refutation prove published minimality"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The declaration is a conditional endpoint. It requires a globally verified 22-state published machine and a checked finite-prefix refutation for every published model with at most 21 states. It supplies no concrete machine table or refutation by itself."))),
                DescribeRole.Theorem)),
        []));
}
