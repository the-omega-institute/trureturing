using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationTopology;

internal sealed class RedundantCoordinateTopologyDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/ObservationTopology/RedundantCoordinateTopology.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A joined coordinate changes topology exactly when it is not recoverable.",
        H("Redundant Coordinate Topology"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("join-topology-equality-is-coordinate-redundancy"),
                DeclarationHandle.Create(
                    Prefix + "join_topology_eq_iff_coordinate_redundant"),
                H("Joining preserves topology exactly for a recoverable coordinate"),
                StatementSource.FromAuthor(RedundancyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Joining the current readout with a candidate coordinate records "
                            + "both values. If the candidate is recoverable from the current "
                            + "readout, this adds no new fibers.")),
                    Paragraph(Text(
                        "Conversely, equality of the joined and current partition topologies "
                            + "makes current-fiber inseparability imply equality of the "
                            + "candidate coordinate.")),
                    Paragraph(Text(
                        "On the displayed inhabited source, the recovery criterion converts "
                            + "that fiber constancy into Refines candidate current. The "
                            + "theorem claims precisely this biconditional."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordinate-inadequacy-is-strict-join-refinement"),
                DeclarationHandle.Create(
                    Prefix + "coordinate_inadequate_iff_strict_join_refinement"),
                H("An unrecoverable coordinate gives exactly a strict join refinement"),
                StatementSource.FromAuthor(StrictFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The joined readout always retains every open set available to the "
                            + "current readout through its first projection.")),
                    Paragraph(Text(
                        "If the candidate coordinate is not recoverable, equality of the two "
                            + "topologies would contradict the redundancy criterion. Their "
                            + "difference supplies an open set available only after joining.")),
                    Paragraph(Text(
                        "Conversely, a recoverable coordinate leaves the topologies equal and "
                            + "is incompatible with strict observation refinement. The "
                            + "equivalence retains the Nonempty source instance."))),
                DescribeRole.Theorem))));

    private static Formula Instance(Formula state) =>
        Seq(OpenBracket, Call("Nonempty", state), CloseBracket);

    private static Formula RedundancyFormula()
    {
        Formula state = F.Id("X");
        Formula currentOutput = F.Id("Current");
        Formula candidateOutput = F.Id("Candidate");
        Formula current = F.Id("current");
        Formula candidate = F.Id("candidate");
        Formula conclusion = Seq(
            Call(
                "partitionTopology",
                Call("conceptJoin", current, candidate)),
            Sp, Eq, Sp, Call("partitionTopology", current), Sp, Iff, Sp,
            Call("Refines", candidate, current));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, current, Colon, Sp, Call("Concept", state, currentOutput),
            Comma, Sp,
            candidate, Colon, Sp, Call("Concept", state, candidateOutput),
            Comma, RowBreak, Grp(),
            Open, Instance(state), Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, conclusion, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula StrictFormula()
    {
        Formula state = F.Id("X");
        Formula currentOutput = F.Id("Current");
        Formula candidateOutput = F.Id("Candidate");
        Formula current = F.Id("current");
        Formula candidate = F.Id("candidate");
        Formula currentTopology = Call("partitionTopology", current);
        Formula joinedTopology = Call(
            "partitionTopology",
            Call("conceptJoin", current, candidate));
        Formula conclusion = Seq(
            Open, Neg, Sp, Call("Refines", candidate, current), Close,
            Sp, Iff, Sp,
            Call(
                "StrictObservationRefinement",
                currentTopology,
                joinedTopology));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, current, Colon, Sp, Call("Concept", state, currentOutput),
            Comma, Sp,
            candidate, Colon, Sp, Call("Concept", state, candidateOutput),
            Comma, RowBreak, Grp(),
            Open, Instance(state), Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, conclusion, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
