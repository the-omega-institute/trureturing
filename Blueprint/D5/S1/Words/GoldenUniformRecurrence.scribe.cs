using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class GoldenUniformRecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Words/GoldenUniformRecurrence",
            "Give an explicit linear window in which every finite golden-word factor recurs."),
        H("Uniform Recurrence of the Golden Word"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-recurrence-bound"),
                DeclarationHandle.Create("D5/S1/Words/GoldenUniformRecurrence.goldenRecurrenceBound"),
                H("The recurrence window is an explicit Fibonacci quantity"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a factor length n, let k be the greatest Fibonacci index with "
                    + "Fib(k) at most n, and define B(n) = 3 Fib(k+5). This bound is "
                    + "deliberately coarse; no optimality claim is made."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("uniform-recurrence-window"),
                DeclarationHandle.Create("D5/S1/Words/GoldenUniformRecurrence.golden_factor_uniformly_recurrent"),
                H("Every factor recurs wholly inside every B(n)-window"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Forall, Sp, F.Id("i"), Comma, Esc, Exists, Sp, F.Id("j"), Comma, Esc,
                                    F.Id("i"), Le, Sp, F.Id("j"), Sp, Land, Sp,
                                    F.Id("j"), Plus, F.Id("n"), Le, Sp, F.Id("i"), Plus,
                                    F.Id("B"), Open, F.Id("n"), Close, Sp, Land, Sp,
                                    F.Id("w"), Eq, Operatorname, Grp(F.Id("goldenFactor")), Open,
                                    F.Id("n"), Comma, F.Id("j"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "For every starting coordinate i and every word w occurring as a "
                                    + "length-n golden factor, there is a start j at or after i such that "
                                    + "w begins at j and ends no later than i+B(n). The proof locates w "
                                    + "inside one control supertile, then finds a complete copy of that "
                                    + "supertile after the arbitrary starting coordinate."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("linear-bound"),
                DeclarationHandle.Create("D5/S1/Words/GoldenUniformRecurrence.golden_recurrenceBound_le"),
                H("The explicit window is at most thirty-nine times the factor length"),
                StatementSource.FromAuthor(Disp(Seq(
                                    F.Id("n"), Gt, D(0), Sp, Rightarrow, Sp,
                                    F.Id("B"), Open, F.Id("n"), Close, Le, D(3, 9), F.Id("n")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "For positive n, Fib(k) is at most n and Fib(k+1) is at most 2n. "
                                    + "The identity Fib(k+5) = 3 Fib(k) + 5 Fib(k+1) therefore gives "
                                    + "B(n) at most 39n."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("direct-linear-window"),
                DeclarationHandle.Create("D5/S1/Words/GoldenUniformRecurrence.golden_factor_uniformly_recurrent_linear"),
                H("Every positive-length factor recurs in a direct 39n window"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Forall, Sp, F.Id("i"), Comma, Esc, Exists, Sp, F.Id("j"), Comma, Esc,
                                    F.Id("i"), Le, Sp, F.Id("j"), Sp, Land, Sp,
                                    F.Id("j"), Plus, F.Id("n"), Le, Sp, F.Id("i"), Plus, D(3, 9), F.Id("n"),
                                    Sp, Land, Sp, F.Id("w"), Eq,
                                    Operatorname, Grp(F.Id("goldenFactor")), Open,
                                    F.Id("n"), Comma, F.Id("j"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "Combining uniform recurrence with the coarse linear estimate removes "
                                    + "the auxiliary Fibonacci expression from the window endpoint."))),
                DescribeRole.Theorem
            )),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Words/GoldenWord")),
        ]));

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);
}
