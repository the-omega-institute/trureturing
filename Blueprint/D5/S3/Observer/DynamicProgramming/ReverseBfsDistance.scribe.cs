using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.DynamicProgramming;

internal sealed class ReverseBfsDistanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reverse breadth-first search computes first-separation depths in quadratic resources.",
        H("Reverse Search for First Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reverse-bfs-correct-and-quadratic"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/DynamicProgramming/ReverseBfsDistance."
                        + "reverse_bfs_correct_and_quadratic"),
                H("Reverse breadth-first search is correct and quadratic"),
                StatementSource.FromAuthor(SearchFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be a finite deterministic state space with update tau and readout "
                            + "q. The pair successor sends each ordered pair to the pair of its "
                            + "updated states, and the initial search table contains exactly the "
                            + "pairs with unequal current readouts.")),
                    Paragraph(Text(
                        "The reverse search expands cumulatively from all initial mismatches. Its "
                            + "output is the first visit depth, with no value for a pair that is "
                            + "never visited. The semantic comparison depth is independently "
                            + "constructed as the first future readout mismatch, again with no "
                            + "value for infinity.")),
                    Paragraph(Text(
                        "The time budget counts one queue visit per ordered pair and one scan per "
                            + "stored reversed edge. The space budget counts that explicit edge "
                            + "table, one distance slot per pair, and a queue with one slot per "
                            + "pair. These constructed budgets are bounded by two and three times "
                            + "the square of the state count, respectively.")),
                    Paragraph(Text(
                        "Correctness follows by identifying the depth-k visited table with pairs "
                            + "having a mismatch witness of length at most k, then comparing the "
                            + "two least witnesses. The explicit reversed edge table has one edge "
                            + "for every ordered state pair."))),
                DescribeRole.Theorem))));

    private static Formula SearchFormula()
    {
        Formula state = F.Id("Y");
        Formula output = F.Id("O");
        Formula update = Tau;
        Formula readout = F.Id("q");
        Formula stateCount = Seq(Lvert, Sp, state, Rvert);
        Formula square = Seq(stateCount, Caret, Grp(D(2)));
        Formula searchDistance = Seq(
            Operatorname, Grp(F.Id("reverseBfsDistance")),
            Open, update, Comma, Sp, readout, Close);
        Formula exactDistance = Seq(
            Operatorname, Grp(F.Id("exactSeparationDepth")),
            Open, update, Comma, Sp, readout, Close);
        Formula time = Seq(
            Operatorname, Grp(F.Id("reverseBfsTimeBudget")), Open, update, Close);
        Formula space = Seq(
            Operatorname, Grp(F.Id("reverseBfsSpaceBudget")), Open, update, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, state, Close,
            CloseBracket, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("DecidableEq")), Open, state, Close,
            CloseBracket, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("DecidableEq")), Open, output, Close,
            CloseBracket, Comma, RowBreak, Grp(),
            update, Colon, Sp, state, Sp, To, Sp, state, Comma, Sp,
            readout, Colon, Sp, state, Sp, To, Sp, output, Comma, RowBreak, Grp(),
            searchDistance, Sp, Eq, Sp, exactDistance, Sp, Land, RowBreak, Grp(),
            time, Sp, Leq, Sp, D(2), Sp, square, Sp, Land, RowBreak, Grp(),
            space, Sp, Leq, Sp, D(3), Sp, square, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
