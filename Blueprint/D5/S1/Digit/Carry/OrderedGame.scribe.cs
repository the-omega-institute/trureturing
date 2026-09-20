using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Carry;

internal sealed class OrderedGameDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite legal ordered path is bounded by its carry reward and initial inversions.",
        H("Ordered Zeckendorf Paths and the Inversion Potential"),
        Blocks(
            Paragraph(Text("A state is one list of natural-number raw W indices. Decode maps "
                + "each index through successor to the positive paper indices; n zeros thus "
                + "represent n ones. Multiplicities are obtained through Multiset.toFinsupp. "
                + "Move records the position of its adjacent window and one of five actions: "
                + "an inversion switch, combining ones, splitting twos, a general split, or "
                + "a consecutive merge. No predecessor map is used.")),
            Describe.Lean(DescribeId.Create("ordered-game-path-potential"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame.path_potential"),
                H("The path potential bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("Path", F.Id("s"), F.Id("t"), F.Id("length"), F.Id("weight")),
                    Sp, Rightarrow, Sp,
                    new Formula.Relation(
                        Add(F.Id("length"), Call("inv", Call("decode", F.Id("t")))),
                        FormulaRelationOperator.LessThanOrEqual,
                        Add(Call("inv", Call("decode", F.Id("s"))), F.Id("weight")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite legal path, actual move count plus "
                    + "final inversions is at most initial inversions plus summed carry reward. "
                    + "Switch reward is zero. In positive indices the other rewards are "
                    + "c1-1, c2-1, c(i-1)+ci-1 for a split at i greater than two, and c(a+1) "
                    + "for a merge at a. Thus rewards include the carry itself. The proof "
                    + "telescopes the existing four local inversion bounds; a switch removes "
                    + "exactly one inversion. There is no terminality or strategy assumption."))),
                DescribeRole.Theorem),
            Paragraph(Text("LGSPath keeps every permitted inversion-switch choice. Its "
                + "priority restarts after every move: switches, leftmost ones, rightmost "
                + "split, then leftmost consecutive merge. Conjecture17 records nonvacuous "
                + "complete LGS existence for every positive n and the comparison of every "
                + "complete LGS run with every legal terminal competitor. That proposition "
                + "is defined but not proved. The path bound alone does not establish "
                + "attainment or weighted greedy optimality.")))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
}
