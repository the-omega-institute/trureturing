using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Apwenian;

internal sealed class GuoHanDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Apwenian/GuoHanDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/guo2025apwenian");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Apwenian sequences, period doubling and uniform substitutions define the classification over finite alphabets with one odd letter.",
        H("Automatic Apwenian Sequences with One Odd Letter"),
        Blocks(
            Node("guo-han-defs-is-apwenian", "The apwenian property", "IsApwenian",
                "A sequence a of nonnegative integers is apwenian when a(0) = 1 and, for every nonnegative integer n, a(n) is congruent to a(2n + 1) + a(2n + 2) modulo two.", DescribeRole.Definition),
            Node("guo-han-defs-period-doubling", "The period-doubling sequence", "periodDoubling",
                "The sequence P of nonnegative integers is defined recursively by P(n) = 1 when n is even and P(n) = 1 - P(floor(n/2)) when n is odd. Thus P(0) = 1, P(2n) = 1 and P(2n + 1) = 1 - P(n). Its entries are zero or one, and it is the fixed point beginning with one of the substitution taking 1 to 10 and 0 to 11.", DescribeRole.Definition),
            Node("guo-han-defs-claim", "The classification statement", "claim",
                "For every finite alphabet Sigma of nonnegative integers containing one and having no other odd letter, every integer p at least two, every p-uniform substitution sigma mapping letters of Sigma to words over Sigma, and every sequence a over Sigma satisfying a(np + r) = sigma(a(n), r) for all nonnegative n and all r from zero through p minus one, a is apwenian if and only if a(n) modulo two equals P(n) for every nonnegative n. Here P is the period-doubling sequence. This is Conjecture 2 in Section 4 of Guo and Han's paper; the equivalence concerns parity and does not identify distinct even letters.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
