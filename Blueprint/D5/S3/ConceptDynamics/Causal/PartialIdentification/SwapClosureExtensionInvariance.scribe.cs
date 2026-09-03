using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class SwapClosureExtensionInvarianceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/"
            + "SwapClosureExtensionInvariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A replayable finite chain of adjacent parent-independent swaps preserves "
            + "structural response profiles and every query readout.",
        H("Swap-Closure Extension Invariance"),
        Blocks(
            Paragraph(Text(
                "One admissible move swaps neighboring nodes whose equations do not read one another. "
                    + "The move records its prefix, pair, suffix, distinctness, and two nonparent certificates.")),
            Paragraph(Text(
                "A typed swap chain is the reflexive-transitive closure of these local moves. "
                    + "Induction composes the state equality supplied by every adjacent swap.")),
            Paragraph(Text(
                "This separates semantic invariance from the remaining combinatorial theorem. "
                    + "Once compatible linear extensions are proved swap-connected, their structural responses and compiled query readouts agree automatically.")),
            Describe.Lean(
                DescribeId.Create("swap-chain-preserves-evaluation"),
                DeclarationHandle.Create(
                    Prefix + "evaluation_invariant_of_swap_chain"),
                H("A finite admissible swap chain preserves evaluation"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The induction proof composes exact final-state equalities for the recorded local moves."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("swap-chain-preserves-response-profile"),
                DeclarationHandle.Create(
                    Prefix + "responseProfile_invariant_of_swap_chain"),
                H("Swap-connected orders have identical response profiles"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The evaluation theorem is applied pointwise to every exogenous state."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("connectivity-implies-extension-invariance"),
                DeclarationHandle.Create(
                    Prefix + "extension_invariance_from_swap_connectivity"),
                H("Swap connectivity discharges global extension invariance"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Any proof that compatible extensions belong to one swap component immediately yields equality of all query readout functions."))),
                DescribeRole.Theorem))));
}
