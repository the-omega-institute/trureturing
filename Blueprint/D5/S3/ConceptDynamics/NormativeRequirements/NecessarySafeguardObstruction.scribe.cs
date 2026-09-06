using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.NormativeRequirements;

internal sealed class NecessarySafeguardObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/NormativeRequirements/NecessarySafeguardObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Necessary requirements constrain permission even when a stated goal or outcome agrees.",
        H("Necessary Safeguard Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("violated-requirement-excludes-permission"),
                DeclarationHandle.Create(Prefix + "violated_requirement_excludes_permission"),
                H("A violated necessary requirement excludes permission"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Permission and the indexed requirements are independent Concept predicates. "
                    + "The premise says every permitted path satisfies every requirement. "
                    + "A witness to a violated requirement therefore excludes that path. "
                    + "This theorem does not select or justify the necessity rule."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rationale-does-not-supply-necessary-safeguard"),
                DeclarationHandle.Create(Prefix + "rationale_does_not_supply_necessary_safeguard"),
                H("Achieving a goal need not suffice for permission"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Given a goal-achieving path that violates a necessary safeguard, that path "
                    + "is excluded and witnesses failure of the universal goal-to-permission rule. "
                    + "Goal achievement is not defined to include permission or the safeguard."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("necessary-safeguard-blocks-readout-factorization"),
                DeclarationHandle.Create(Prefix + "necessary_safeguard_blocks_readout_factorization"),
                H("A missing safeguard obstructs an outcome-only decision"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two paths have equal outcome readouts. One is permitted; the other violates "
                    + "a necessary safeguard. Their distinct permission values are derived, then "
                    + "the existing history-sensitive outcome factorization theorem is applied. "
                    + "A natural-number capacity and parity example supplies inhabited premises. "
                    + "Consent, rights, safety, and authorization can instantiate the predicates, "
                    + "but real-world facts and the authority of a normative standard are not proved."))),
                DescribeRole.Theorem))));
}
