using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class GuardedPhaseExecutionDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Guarded weighted paths characterize finite executions on one original source.",
        H("Guarded Phase Execution"),
        Blocks(
            Paragraph(Text(
                "A fixed instruction table uses control states Q, addresses A and replies R. "
                + "One observation field assigns a reply to each epoch and address. "
                + "For an original source u with transport U, the intended field is the literal "
                + "read on U iterated j times at epoch j. The same field is used in every phase.")),
            Describe.Lean(
                DescribeId.Create("instruction"), Handle("Instruction"),
                H("Literal reads, unit updates and halts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A read instruction installs one address and a successor for every reply. "
                    + "An update has one successor and increments the epoch by one. A halt has "
                    + "no outgoing edge. The instruction table does not inspect the source or epoch."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-run"), Handle("Run"),
                H("Finite actual paths"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An actual path keeps its initial and terminal controls and epochs. Reads "
                    + "use the fixed source's observation field at the current epoch; updates "
                    + "advance that epoch exactly once. The empty path is allowed. A path ending "
                    + "at a halt cannot have passed through an earlier halt."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fixed-path"), Handle("FixedPath"),
                H("Paths under one fixed response vector"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every read uses the chosen response vector. The weight records exactly "
                    + "the number of updates, with zero contribution from reads. Endpoints are "
                    + "retained, including cuts inside update-containing cycles."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("crossing"), Handle("Crossing"),
                H("A boundary is crossed by a final update"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A crossing consists of a fixed-response path followed by one update. "
                    + "Its total weight is one plus the preceding path's weight. Consequently "
                    + "all reads occur strictly before the endpoint epoch. A pure-read cycle "
                    + "cannot supply a crossing into a later epoch."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("guard"), Handle("Guard"),
                H("One source supplies the whole phase"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The guard requires equality of the observation field and the response "
                    + "vector at every epoch in a half-open interval. Addresses can be labels "
                    + "for the installed read states, so this asserts exactly the common "
                    + "response vector without adding an online simultaneous-read instruction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("partition"), Handle("Partition"),
                H("Strict phase boundaries and a terminal delimiter"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A nonempty list records each interval's right endpoint and response vector. "
                    + "Endpoints increase strictly, adjacent intervals meet, every interval "
                    + "satisfies its guard, and the final endpoint is the specified delimiter. "
                    + "Adjacent vectors may agree; maximality is not required."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("phase-paths"), Handle("PhasePaths"),
                H("Endpoint-compatible phase certificates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every internal segment is a crossing to the next phase's starting control. "
                    + "The final segment is a fixed-response path to the requested terminal "
                    + "control and epoch J. Its delimiter is J plus one, which includes reads "
                    + "at J and does not perform an update after halt. This last path may be empty."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("guarded-phase-execution"), Handle("guarded_phase_execution"),
                H("Exact equivalence with actual execution"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every guarded partition from the starting epoch through J, "
                        + "phase paths exist exactly when an actual finite path connects the "
                        + "same initial and terminal controls at those epochs. This holds for "
                        + "arbitrary state, address and reply types; finiteness is unnecessary "
                        + "for the semantic equivalence.")),
                    Paragraph(Text(
                        "To split an actual path, locate the unit update that first enters an "
                        + "internal boundary epoch. The preceding segment ends one epoch before "
                        + "the boundary, so its entire read range satisfies the old guard. "
                        + "Repeat on the remaining actual path. Conversely, each guard converts "
                        + "its fixed-response path into actual steps, and the exact endpoints "
                        + "allow their concatenation.")),
                    Paragraph(Text(
                        "When the terminal control is a halt, the equivalence is about its "
                        + "first arrival. It imposes no action-count bound and no termination "
                        + "assumption. A finite bound on the number of phases and an effective "
                        + "arithmetic description of fixed-response paths are separate hypotheses "
                        + "needed for a uniform arithmetic synthesis procedure."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(Owner + name);
}
