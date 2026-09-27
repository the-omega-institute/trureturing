using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Carry;

internal sealed class OrderedGameDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concrete greedy continuation, weighted split promotion and finite cascade exchanges.",
        H("Ordered Zeckendorf Paths and the Inversion Potential"),
        Blocks(
            Paragraph(Text("A state is one list of natural-number raw W indices. Decode maps "
                + "each index through successor to the positive paper indices; n zeros thus "
                + "represent n ones. Multiplicities are obtained through Multiset.toFinsupp. "
                + "Move records the position of its adjacent window and one of five actions: "
                + "an inversion switch, combining ones, splitting twos, a general split, or "
                + "a consecutive merge. No predecessor map is used.")),
            Describe.Lean(DescribeId.Create("ordered-game-greedy-attainment"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame.greedy_attainment"),
                H("Concrete greedy continuation attains its reward"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("c"), Comma, Sp, Exists, Sp, F.Id("d"), Comma, Sp,
                    Call("RawGreedyPath", F.Id("c"), F.Id("d"), Call("G", F.Id("c"))),
                    Sp, Land, Sp, Call("CanonicalRaw", F.Id("d"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite raw multiplicity state, the concrete "
                    + "continuation G is attained by a finite RawGreedyPath to binary nonadjacent "
                    + "digits. Each decision combines ones first, otherwise splits the highest "
                    + "duplicate, otherwise merges the least occupied consecutive pair. Priority "
                    + "is recomputed after every move. G recurses on the existing strict carry "
                    + "measure and is not defined as a maximum over paths. Labels remain data. "
                    + "This establishes raw attainment, not the comparison with competitors or "
                    + "ordered LGS completion."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-game-complete-greedy-reward"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame.complete_greedy_reward"),
                H("Every complete raw greedy path has the same reward"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("RawGreedyPath", F.Id("c"), F.Id("e"), F.Id("w")),
                    Sp, Land, Sp, Call("CanonicalRaw", F.Id("e")),
                    Sp, Rightarrow, Sp, Eq(F.Id("w"), Call("G", F.Id("c")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every complete raw path obeying the stated priorities "
                    + "has reward G at its initial state. Legality and priority determine the "
                    + "first action and successor uniquely: ones exclude every other preferred "
                    + "action, otherwise the highest duplicate fixes the split, and a binary "
                    + "state fixes the least consecutive merge. Induction along the actual path "
                    + "then agrees with the recursive continuation. A canonical endpoint admits "
                    + "no carry. This equality covers all complete RawGreedyPath witnesses; "
                    + "it does not compare an arbitrary legal competitor with G."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-game-shared-input-merge-repair"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame.shared_input_merge_repair"),
                H("All five shared-input merge repairs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With unrestricted spectators, a legal merge sharing an "
                    + "input with an enabled split has a split-first legal path to the exact merge "
                    + "endpoint. If the lower input is duplicated it is split first; otherwise the "
                    + "upper input is split. In positive paper indices the lower-input detours "
                    + "are S1;S2, S2;S3;S1, and Sa;S(a+1);C(a-2), with gains c1-1, "
                    + "2c2+c1-2, and 2c(a-1)+2ca-2. The upper-input detours are S2;S1 "
                    + "at a=1, gaining zero, and S(a+1);C(a-1) at a>=2, gaining one. "
                    + "The theorem gives exact reward equality with a natural-number gain. "
                    + "Replacement tails are legal; no greedy-tail assertion is made."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-game-ones-terminal-promotion"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame.ones_terminal_promotion"),
                H("Ones first against arbitrary interleaved terminal paths"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("RawPath", F.Id("c"), F.Id("e"), F.Id("w")), Sp, Land, Sp,
                    Call("CanonicalRaw", F.Id("e")), Sp, Land, Sp,
                    Call("SplitStep", D(0), F.Id("c"), F.Id("cPrime")), Sp, Rightarrow, Sp,
                    Exists, Sp, F.Id("v"), Comma, Sp,
                    Call("RawPath", F.Id("cPrime"), F.Id("e"), F.Id("v")), Sp, Land, Sp,
                    new Formula.Relation(F.Id("w"), FormulaRelationOperator.LessThanOrEqual,
                        Add(Call("splitReward", F.Id("c"), D(0)), F.Id("v")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If combining ones is enabled, every raw path to binary "
                    + "nonadjacent digits can be replaced by one beginning with that split, "
                    + "retaining its endpoint and at least its full reward. The competing path "
                    + "may interleave merges and splits arbitrarily. The proof promotes ones "
                    + "through split steps, repairs a merge consuming a one, and commutes past "
                    + "higher merges. This closes the ones-first promotion branch. The dependent "
                    + "Optimality module supplies the nonzero-split and least-binary-merge "
                    + "comparisons inside its complete raw terminal bound."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-game-split-greedy-terminal-promotion"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame.split_greedy_terminal_promotion"),
                H("Promote the preferred split through the actual initial split phase"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A competing split followed by a complete raw greedy path "
                    + "admits a legal replacement beginning with the currently highest split, "
                    + "with the same terminal endpoint and at least its reward. The proof cuts "
                    + "the actual greedy continuation immediately before its first merge, or "
                    + "at its canonical endpoint. The cut state is binary. Only that complete "
                    + "WeightedSplitPath is passed to split_phase_promotion; the entire remaining "
                    + "raw suffix is preserved. No split-only comparison is applied across merges."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-game-high-cascade"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame.high_cascade"),
                H("Finite high cascade and boundary-independent legal replay"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive raw k, assume holes at k and k+1, at most "
                    + "two tokens at k+2, binary digits above k+2 and at most one zero. A finite "
                    + "greedy split cascade makes the tail at and above k binary and preserves "
                    + "all lower coordinates. Finite support supplies the first zero; induction "
                    + "on its distance proves the coordinate invariant. Every split has unit "
                    + "reward. The same word replays from any state agreeing strictly above k, "
                    + "with the same reward and exact additive endpoint balance. Lower coordinates "
                    + "in the replay are unrestricted; its moves are not asserted to be greedy."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-game-path-raw-erasure"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame.path_raw_erasure"),
                H("Erasure preserves the complete reward"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("Path", F.Id("s"), F.Id("t"), F.Id("length"), F.Id("weight")),
                    Sp, Rightarrow, Sp,
                    Call("RawPath", Call("rawCounts", F.Id("s")),
                        Call("rawCounts", F.Id("t")), F.Id("weight"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite legal ordered path erases to a labelled raw "
                    + "path with exactly the same accumulated reward. Switches preserve multiplicities "
                    + "and contribute zero reward. Each remaining label retains its actual CarryStep "
                    + "and its consumed and produced digits in the same spectator context. Labels "
                    + "are explicit and are not reconstructed from an unlabelled proposition. "
                    + "The theorem neither assumes terminality nor asserts optimality."))),
                DescribeRole.Theorem),
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
                + "complete LGS run with every legal terminal competitor. Its proof is "
                + "OrderedGame/Completion.result, which combines these path bounds with "
                + "ordered attainment, raw greedy optimality and finite completion.")))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
