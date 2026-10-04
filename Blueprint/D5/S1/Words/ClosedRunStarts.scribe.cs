using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class ClosedRunStartsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identify literal forbidden blocks with the bounded-run scanner and run-start count.",
        H("Run Starts in a Closed Boolean Word"),
        Blocks(
            Paragraph(Text(
                "A word has n Boolean coordinates. TrueBlock(w,s,k) requires s+k at most n "
                + "and every coordinate in [s,s+k) to be true. RunStart adds a false "
                + "predecessor at s-1 when s is positive; at zero it adds no predecessor. "
                + "The count sums these start indicators over exactly n-k+1 positions.")),
            Describe.Lean(
                DescribeId.Create("closed-word-run-start-equivalence"),
                DeclarationHandle.Create(
                    "D5/S1/Words/ClosedRunStarts.closed_word_run_start_equivalence"),
                H("Scanner, forbidden blocks, and zero run starts"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Comma, F.Id("k"), InMacro,
                    Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(0), Lt, F.Id("k"), Le, Sp, F.Id("n"), Implies, Sp,
                    Forall, Sp, F.Id("w"), Colon, Sp, F.Id("Fin"), Open,
                    F.Id("n"), Close, To, Sp, F.Id("Bool"), Comma, Sp,
                    Open, Operatorname, Grp(F.Id("DBonacciAdmissible")), Open,
                    F.Id("k"), Comma, F.Id("n"), Comma, F.Id("w"), Close,
                    Iff, Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("N")),
                    Comma, Neg, Operatorname, Grp(F.Id("TrueBlock")), Open,
                    F.Id("w"), Comma, F.Id("s"), Comma, F.Id("k"), Close, Close,
                    Sp, Land, Sp, Open,
                    Open, Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("N")),
                    Comma, Neg, Operatorname, Grp(F.Id("TrueBlock")), Open,
                    F.Id("w"), Comma, F.Id("s"), Comma, F.Id("k"), Close, Close,
                    Iff, Operatorname, Grp(F.Id("startCount")), Open,
                    F.Id("k"), Comma, F.Id("w"), Close, Eq, D(0), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Induction on the word length tracks the scanner's remaining true-bit "
                    + "budget together with all full forbidden windows. For the start count, "
                    + "the earliest forbidden block either starts at zero or has a false "
                    + "predecessor: a true predecessor would produce an earlier block. "
                    + "The argument includes a block ending at the final coordinate and "
                    + "the boundary case n=k."))),
                DescribeRole.Theorem))));
}
