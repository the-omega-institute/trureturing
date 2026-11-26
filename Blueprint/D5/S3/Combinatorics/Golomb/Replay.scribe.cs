using static StrataLint.Scribe.DefinitionDsl;
using StrataLint.Engine;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Golomb;

internal sealed class GolombReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Golomb/Replay.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/notik2026singergolomb");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader("D5/S3/Combinatorics/Golomb/Replay",
            "Separated real distances justify the orientation and every row of a checked bound tree.",
            "kernel-replayed-certificate", Anchor.ParseCanonical("mathlib/module/Mathlib.Basic.Real.Basic")),
        H("Real Golomb ruler bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golomb-real-ruler"),
                DeclarationHandle.Create(Prefix + "RealGolomb"),
                H("Separated distances on an ordered tuple"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a tuple of k + 1 real marks, every positive index pair has distance at least one. "
                    + "Distances of two distinct positive index pairs differ in absolute value by at least one. "
                    + "The first condition already gives strict increase. The length is the last mark minus the first."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golomb-bound-tree-sound"),
                DeclarationHandle.Create(Prefix + "check_sound"),
                H("An accepted tree bounds the total gap length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Every admissible separation relation covers the two signs used at a branch. "
                    + "A nonnegative combination of valid inequalities either proves a scaled lower bound "
                    + "or gives a contradiction. At equality with the target, the route ends at a bound leaf "
                    + "whose weighted right-hand side equals the scaled target and whose positively weighted rows are tight."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golomb-replay-marks"),
                DeclarationHandle.Create(Prefix + "replay_marks"),
                H("The verified bound holds in both orientations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Consecutive gaps express the distance of every span as a contiguous sum. Static rows "
                    + "are justified by unit distances, smaller-ruler bounds, or the triangular lower bound "
                    + "for separated distances. The first and last gaps are separated for at least three marks. "
                    + "One orientation satisfies the archive's prescribed sign, and reflection preserves length."))),
                DescribeRole.Theorem)), []));
}
