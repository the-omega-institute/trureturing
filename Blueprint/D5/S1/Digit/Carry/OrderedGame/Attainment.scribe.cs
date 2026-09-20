using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Carry.OrderedGame;

internal sealed class AttainmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact ordered strategy accounting and arbitrary-order switch normalization.",
        H("Ordered Attainment"),
        Blocks(
            Paragraph(Text("This component concerns the Long Game Strategy of Definition 1.6 "
                + "and Conjecture 1.7 in The Ordered Zeckendorf Game, arXiv:2508.20222v2. "
                + "It uses the existing raw-index Move, Preferred, Path and LGSPath without "
                + "changing their priorities or selecting a particular switching algorithm. "
                + "Positive source indices are obtained by mapping successor.")),
            Describe.Lean(DescribeId.Create("ordered-attainment-zero-inversions"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame/Attainment.inversions_zero_iff_sorted"),
                H("Zero inversions characterize sorted states"),
                StatementSource.FromAuthor(Disp(Seq(
                    Eq(Call("inv", Call("decode", F.Id("s"))), D(0)), Sp,
                    Iff, Sp, Call("Pairwise", F.Id("le"), F.Id("s"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every raw state, the existing positive-index inversion "
                    + "counter is zero exactly when the raw list is nondecreasing. The proof "
                    + "inducts on the actual list and its smaller-tail count."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-attainment-move-potential"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame/Attainment.lgs_move_potential"),
                H("Selected moves attain the full reward"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("LGSMove", F.Id("p"), F.Id("a"), F.Id("s"), F.Id("t")), Sp,
                    Rightarrow, Sp, Eq(Add(D(1), Call("inv", Call("decode", F.Id("t")))),
                        Add(Call("inv", Call("decode", F.Id("s"))), Call("reward", F.Id("s"), F.Id("a"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every selected carry starts sorted because any adjacent "
                    + "inversion would have higher priority. Leftmost selection of ones forces "
                    + "their prefix to be empty, which is essential to equality. The remaining "
                    + "cases compute the exact spectator counts on both sides of the selected "
                    + "window. Every permitted switch removes exactly one inversion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-attainment-path-potential"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame/Attainment.lgs_path_potential"),
                H("Every strategy path telescopes exactly"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("LGSPath", F.Id("s"), F.Id("t"), F.Id("length"), F.Id("weight")), Sp,
                    Rightarrow, Sp, Eq(Add(F.Id("length"), Call("inv", Call("decode", F.Id("t")))),
                        Add(Call("inv", Call("decode", F.Id("s"))), F.Id("weight")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("No assumption on initial sortedness or terminality is "
                    + "needed. For sorted initial and terminal final states, actual move count "
                    + "equals accumulated carry reward. This equality does not compare that "
                    + "reward with a competing raw carry strategy."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-attainment-switch-normalization"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame/Attainment.switch_normalization"),
                H("Switch completion and order independence"),
                StatementSource.FromAuthor(Disp(SwitchStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every start there exists a sorted permutation reached "
                    + "by an LGS path of zero reward and exactly the initial inversion count "
                    + "moves. Every legal zero-reward path with no remaining switch has that "
                    + "same endpoint and length and preserves all raw multiplicities. Every "
                    + "carry has positive reward, so zero-reward paths are precisely switch "
                    + "phases. Strong induction on inversions constructs completion; the proof "
                    + "retains all allowed switch orders."))), DescribeRole.Theorem),
            Paragraph(Text("These attainment components feed the full Conjecture 1.7 proof "
                + "in OrderedGame/Completion.result. Raw weighted domination is supplied by "
                + "OrderedGame/Optimality, and Completion supplies priority correspondence "
                + "and finite ordered completion. Independent review and first-freeze "
                + "admission remain pending; no worldwide priority is claimed.")))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula SwitchStatement() => Seq(
        Forall, Sp, F.Id("s"), Sp, Exists, Sp, F.Id("t"), Sp,
        Call("LGSPath", F.Id("s"), F.Id("t"), Call("inv", Call("decode", F.Id("s"))), D(0)),
        Sp, Land, Sp, Call("Pairwise", F.Id("le"), F.Id("t")),
        Sp, Land, Sp, Call("Perm", F.Id("s"), F.Id("t")), Sp, Land, Sp,
        Forall, Sp, F.Id("u"), Sp, F.Id("length"), Sp,
        Call("Path", F.Id("s"), F.Id("u"), F.Id("length"), D(0)), Sp, Rightarrow, Sp,
        Grp(Forall, Sp, F.Id("p"), Sp, F.Id("v"), Sp, Neg, Sp,
            Call("Move", F.Id("p"), F.Id("switch"), F.Id("u"), F.Id("v"))),
        Sp, Rightarrow, Sp, Eq(F.Id("u"), F.Id("t")), Sp, Land, Sp,
        Eq(F.Id("length"), Call("inv", Call("decode", F.Id("s")))), Sp, Land, Sp,
        Eq(Call("rawCounts", F.Id("u")), Call("rawCounts", F.Id("s"))));
}
