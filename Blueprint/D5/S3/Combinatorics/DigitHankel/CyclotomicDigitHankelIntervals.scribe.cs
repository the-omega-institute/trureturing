using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DigitHankel;

internal sealed class CyclotomicDigitHankelIntervalsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelIntervals.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/sobolewski2026hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary Run Intervals for Cyclotomic Zeros",
        H("Binary Run Intervals for Cyclotomic Zeros"),
        Blocks(
            Node("cyclotomic-digit-hankel-intervals-run-value", "Binary run value", "runValue", "For a Boolean starting bit and a list of positive run lengths, runValue recursively encodes the alternating binary runs as a natural number; the true and false branches occupy complementary blocks.", DescribeRole.Definition),
            Node("cyclotomic-digit-hankel-intervals-run-admissible", "Admissible run language", "RunAdmissible", "RunAdmissible d describes the surviving run lists: a one-run list has length at most d, a two-run list has both lengths at most d with one strictly shorter, and every longer list has each internal leading run strictly shorter than d.", DescribeRole.Definition),
            Node("cyclotomic-digit-hankel-intervals-forbidden", "Forbidden runs lie in zero intervals", "forbidden_runs_mem", "For d at least two and m positive, if every nonempty positive run expansion with value m is inadmissible, then m plus one belongs to the cyclotomic zero set for d.", DescribeRole.Theorem),
            Node("cyclotomic-digit-hankel-intervals-survival", "Run survival induction", "run_survival", "Suppose a predicate on a starting phase and a positive run list satisfies the terminal, deletion, reflection, and singular transition rules. Then its value at phase one is equivalent to RunAdmissible d for every nonempty positive run list.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
