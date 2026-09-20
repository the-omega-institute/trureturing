using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Carry;

internal sealed class SplitStabilizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite raw split phases stabilize with unique firing counts and endpoint.",
        H("Least Action for Zeckendorf Split Phases"),
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
                + "carry measure. These conclusions compare firing counts, not weighted "
                + "rewards; ordered longest-game optimality is not established here."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("split-stabilization-" + name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S1/Digit/Carry/SplitStabilization." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Call(string name, params string[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments.Select(F.Id)]);
}
