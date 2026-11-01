using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class NamedPathDurationReconstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive additive duration detects all rooted named paths exactly in the absence of branching.",
        H("Named Paths and Positive Duration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("named-path-duration-reconstruction"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Spacetime/NamedPathDurationReconstruction.readout_injective_iff_no_branching"),
                H("Recurrent branching is exactly the reconstruction obstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V be any quiver, let r be a fixed root, and assign a strictly positive "
                        + "real duration to every actual arrow. Suppose a finite path exists between "
                        + "every ordered pair of vertices. On the dependent sum of all finite paths "
                        + "starting at r, the pair consisting of endpoint and summed duration is "
                        + "injective if and only if, at every vertex a, the dependent sum of all "
                        + "arrows a to b over all targets b is a subsingleton. Arrows retain their "
                        + "names: parallel arrows are separate choices. Empty paths and empty return "
                        + "segments are included. No finiteness or rational independence is assumed.")),
                    Paragraph(Text(
                        "For necessity, two distinct outgoing arrows at a recurrent vertex extend "
                        + "to two nonempty return blocks U and W. Following a rooted prefix by UW "
                        + "or WU gives equal endpoint and duration. Prefix cancellation and the "
                        + "first named edge distinguish the paths. For sufficiency, unique outgoing "
                        + "arrows force the same first edge of two nonempty paths. Cancel its "
                        + "duration and induct on path length; positivity separates the empty path "
                        + "from every nonempty path. The one-vertex one-loop graph is included, "
                        + "as is the one-vertex graph with no arrows, whose only path is empty.")),
                    Paragraph(Text(
                        "This is the structural no-branching intermediate of Theorem 3.1 in "
                        + "Recursive Relational Observation: Typed Residual Cocycles and Ordered-Path "
                        + "Reconstruction. The theorem operates directly on actual quiver paths. "
                        + "The finite nonempty-edge hypothesis needed to turn unique outgoing "
                        + "arrows into an exhaustive single-cycle enumeration, the explicit "
                        + "lap-and-suffix reconstruction formula, and the lifting of such paths "
                        + "to concrete typed source executions remain separate obligations. "
                        + "The result supplies no physical clock realization, finite-precision "
                        + "algorithm, resource bound or whole-source closure."))),
                DescribeRole.Theorem))));
}
