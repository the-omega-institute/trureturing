using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Carry;

internal sealed class SplitStabilizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite raw split phases stabilize, and greedy split phases maximize full reward.",
        H("Least Action and Weighted Greedy Zeckendorf Split Phases"),
        Blocks(
            Paragraph(Text("Indices are zero-based. A split consumes two tokens at its index. "
                + "Its output is one token at 1 for index 0, tokens at 0 and 2 for index 1, "
                + "and tokens at i and i+3 for index i+2. SplitPath retains a finite chronological "
                + "list of legal split indices and all spectator multiplicities. Stable means "
                + "that every multiplicity is at most one; adjacent occupied sites may remain.")),
            Node("split_path_balance", "Exact site balance",
                Seq(Call("SplitPath", "c", "d", "xs"), Sp, Rightarrow, Sp,
                    Forall, Sp, F.Id("j"), Comma, Sp,
                    Call("d", "j"), Sp, Plus, Sp, D(2), Sp, Times, Sp, Call("count", "xs", "j"),
                    Sp, Eq, Sp, Call("c", "j"), Sp, Plus, Sp, Call("incoming", "xs", "j")),
                "For every legal phase and every site j, final occupancy plus twice the "
                + "firing count equals initial occupancy plus received tokens. The incoming "
                + "count is count(xs,1)+count(xs,2) at zero, count(xs,0)+count(xs,3) at one, "
                + "and count(xs,j-1)+count(xs,j+2) at j at least two."),
            Node("split_stabilization", "Least action and uniqueness",
                Seq(Call("SplitPath", "c", "d", "xs"), Sp, Land, Sp,
                    Call("SplitPath", "c", "e", "ys"), Sp, Land, Sp,
                    Call("Stable", "e"), Sp, Rightarrow, Sp,
                    Forall, Sp, F.Id("j"), Comma, Sp,
                    new Formula.Relation(Call("count", "xs", "j"),
                        FormulaRelationOperator.LessThanOrEqual, Call("count", "ys", "j"))),
                "Every legal phase fires each site at most as often as any stabilizing phase "
                + "from the same start. If both phases stabilize, their firing counts and "
                + "endpoints are equal. At a first attempted excess firing, the balance "
                + "equation and nonnegative incoming contributions would leave at most one "
                + "token at the firing site, contradicting legality."),
            Node("exists_split_stabilization", "Complete split phases exist",
                Seq(Call("SplitPath", "start", "c", "xs"), Sp, Rightarrow, Sp,
                    Exists, Sp, F.Id("d"), Sp, F.Id("ys"), Comma, Sp,
                    Call("SplitPath", "start", "d", "ys"), Sp, Land, Sp, Call("Stable", "d")),
                "Given a legal prefix, a finite stabilizing split phase exists from the same "
                + "start. The recursive construction continues at the prefix endpoint. An enabled "
                + "split is a carry step, so recursion decreases the existing lexicographic "
                + "carry measure. The conclusion asserts existence from the same start; "
                + "it does not expose an extension witness for the supplied prefix."),
            Node("split_prefix_promotion", "Legal weighted replay across a prefix",
                Seq(Call("WeightedSplitPath", "c", "d", "xs", "w"), Sp, Land, Sp,
                    Call("Enabled", "c", "j"), Sp, Land, Sp,
                    Call("CrossablePrefix", "xs", "j"), Sp, Rightarrow, Sp,
                    Call("PromotedLegalReplay", "c", "d", "xs", "j")),
                "If j is enabled and every prefix index differs from j and is below j, "
                + "the split at j can move before the prefix without decreasing total reward. "
                + "Index zero can instead cross every other index. Both orders have a common "
                + "endpoint after firing j and replaying the prefix; replay is legal but need "
                + "not be greedy. Rewards include the carry and all subsequent sorting switches."),
            Node("split_phase_promotion", "Preferred first split in a complete phase",
                Seq(Call("CompleteWeightedSplitPhase", "c", "d", "w"), Sp, Land, Sp,
                    Call("EnabledZeroOrHighest", "c", "j"), Sp, Rightarrow, Sp,
                    Call("PreferredFirstReplay", "c", "d", "j")),
                "Choose an enabled split j which is zero or has no duplicate above it. "
                + "The first-overfire bound forces this split to occur in every stabilizing "
                + "phase. Extracting its first occurrence gives a legal phase with the same "
                + "endpoint and no smaller reward, beginning with the chosen split."),
            Node("greedy_split_optimality", "Greedy split phases maximize reward",
                Seq(Call("GreedySplitPath", "c", "e", "g"), Sp, Land, Sp,
                    Call("Stable", "e"), Sp, Land, Sp,
                    Call("WeightedSplitPath", "c", "d", "xs", "w"), Sp, Land, Sp,
                    Call("Stable", "d"), Sp, Rightarrow, Sp,
                    new Formula.Relation(F.Id("w"), FormulaRelationOperator.LessThanOrEqual, F.Id("g"))),
                "For every raw start and every complete greedy split phase, each complete "
                + "competing split phase has no greater full reward. Greedy priority selects "
                + "ones first and otherwise the highest duplicate, recomputed after each split. "
                + "The proof repeatedly promotes the selected first split and inducts on the "
                + "greedy continuation. Binary endpoints can still admit merges. No comparison "
                + "with paths containing merges, or complete ordered-game optimality, follows here."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("split-stabilization-" + name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S1/Digit/Carry/SplitStabilization." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Call(string name, params string[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments.Select(F.Id)]);
}
