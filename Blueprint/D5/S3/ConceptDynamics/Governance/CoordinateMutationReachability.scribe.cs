using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Governance;

internal sealed class CoordinateMutationReachabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite coordinate mutations connect exactly states with finite disagreement "
            + "and identical protected coordinates.",
        H("Coordinate Mutation Reachability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coordinate-reachable-iff-finite-difference"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Governance/CoordinateMutationReachability."
                        + "coordinate_reachable_iff_finite_difference"),
                H("Exact connected components of coordinate mutations"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A state assigns a value of its own type to every key. A legal step "
                            + "may change one unprotected key and must leave every other key "
                            + "unchanged. All product states are allowed: cross-key validation "
                            + "constraints are not part of this model.")),
                    Paragraph(Text(
                        "A finite path exists exactly when the endpoints agree at every "
                            + "protected key and differ at only finitely many keys. The reverse "
                            + "direction constructs the path by replacing differing coordinates. "
                            + "The forward direction accumulates the finite support of its steps.")),
                    Paragraph(Text(
                        "For projection partitioning, protect the input key belonging to the "
                            + "output shard. If the producer preserves that output on every legal "
                            + "step, it preserves the output along every such path. With finitely "
                            + "many input keys this yields dependence on the protected key alone. "
                            + "For infinitely many keys the finite-disagreement condition is essential.")),
                    Paragraph(Text(
                        "Counting changed output files alone does not supply that invariance. "
                            + "For Boolean inputs, the producer (a, b) mapped to (a XOR b, false) "
                            + "changes exactly one output when either input is flipped, yet its "
                            + "first output depends on both inputs. The shard-to-key association "
                            + "must therefore be checked in addition to the changed-file count.")),
                    Paragraph(Text(
                        "This result does not certify a producer, a hash function, or the "
                            + "completeness of a mutation test suite. It does not turn 'at most "
                            + "one changed output' into 'exactly one': detecting every genuine "
                            + "input change additionally requires injectivity of the local output."))),
                DescribeRole.Theorem))));
}
