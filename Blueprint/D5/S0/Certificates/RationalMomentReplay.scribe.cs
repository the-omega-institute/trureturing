using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class RationalMomentReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/RationalMomentReplay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite elimination trace is replayed against current weights. Every successful step preserves the same moments and removes support; the final dimension-dependent bound is checked separately.",
        H("Exact rational compression replay"),
        Blocks(
            Describe.Lean(DescribeId.Create("replay-steps"),
                DeclarationHandle.Create(Prefix + "replaySteps"), H("Structurally recursive replay"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Terminates on every finite input list and returns failure at the first invalid step. It does not discover null directions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("replay-sound"),
                DeclarationHandle.Create(Prefix + "replaySteps_sound"), H("Trace-wide invariants"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Successful replay preserves nonnegativity, total mass, and all nominated moments. The final support is contained in the initial support, and each step consumes at least one support point."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("support-positive"),
                DeclarationHandle.Create(Prefix + "activeAtoms_card_pos_of_total_one"), H("Normalized vectors retain an atom"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite vector whose total is one cannot have empty nonzero support."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("trace-length"),
                DeclarationHandle.Create(Prefix + "replaySteps_length_lt_initial_support"), H("Bound successful trace length"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Starting from N active atoms in a probability vector, a successful trace has at most N-1 steps. This bounds accepted steps, not rational arithmetic bit complexity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("check-compression"),
                DeclarationHandle.Create(Prefix + "checkCompression"), H("Complete certificate consumer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Checks initial normalization and nonnegativity, replays the supplied trace, and requires final support at most the number of retained features plus one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("compression-sound"),
                DeclarationHandle.Create(Prefix + "checkCompression_sound"), H("Certified sparse probability output"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Acceptance yields a normalized nonnegative output with the same feature moments, contained support, and the stated terminal support bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("support-predicate"),
                DeclarationHandle.Create(Prefix + "checkCompression_preserves_support_predicate"), H("Preserve arbitrary support admissibility"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every predicate satisfied by all initial nonzero atoms remains true for all output nonzero atoms. The predicate need not be linear or decidable."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mean-example"),
                DeclarationHandle.Create(Prefix + "mean_preserving_replay_example"), H("Closed exact accepted example"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A three-atom uniform law compresses to its middle atom while preserving its mean. The source includes an ordinary decide proof of the closed checker result."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reactivation-rejection"),
                DeclarationHandle.Create(Prefix + "rejects_zero_atom_reactivation"), H("Reject a forbidden support revival"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A direction preserving mean and total would move mass into an initially zero middle atom. The inactive-coordinate check rejects that payload."))), DescribeRole.Theorem))));
}
