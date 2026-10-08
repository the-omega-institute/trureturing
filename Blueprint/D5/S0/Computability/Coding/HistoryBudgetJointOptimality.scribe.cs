using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Coding;

internal sealed class HistoryBudgetJointOptimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An extreme iid law and one infinite greedy code attain the history-class joint maximum.",
        H("Joint Optimization over History Processes and Prefix Codes"),
        Blocks(
            Paragraph(Text("Let A have d at least two letters. Fix a letter called base and a real "
                + "lower bound delta with 0 < delta and d times delta at most one. Admissible(delta,q) "
                + "means that every finite history h has a row q(h,a) whose coordinates are at least "
                + "delta and sum to one. There is no stationarity, finite-memory, mixing or computability "
                + "hypothesis. A word mass is the product of the rows encountered along its actual path.")),
            Paragraph(Text("Write p for the extreme row: its base coordinate is 1 - (d-1)delta and "
                + "every other coordinate is delta. For arbitrary natural depth budgets b and fixed "
                + "tie orders, G is the canonical infinite iid greedy code for p. Legal(b,F), its levels, "
                + "the iid truncated mass T(p,F,N), and the countable iid mass S(p,F) are the existing "
                + "prefix-code constructions. The history versions replace iid products with actual "
                + "conditional path products. J is the set of all S(q,F) with q admissible and F legal. "
                + "Countable masses and their supremum lie in the extended nonnegative reals and are at most one. "
                + "Their real-valued complement is consequently also one minus this optimum.")),
            Describe.Lean(
                DescribeId.Create("history-budget-joint-optimality"),
                DeclarationHandle.Create("D5/S0/Computability/Coding/HistoryBudgetJointOptimality.result"),
                H("The same iid process and code attain the joint optimum"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Finite path sums satisfy a backward recursion with an indicator "
                        + "reward at selected nodes. After reserving delta in every coordinate, the "
                        + "remaining row mass is placed on a child of maximum continuation value. "
                        + "Backward induction bounds every process. Choosing the remaining horizon "
                        + "from each node's depth defines one process on all histories and attains "
                        + "all relevant backward values simultaneously.")),
                    Paragraph(Text("Swap the maximizing child at each original history with base. "
                        + "The resulting tree bijection preserves prefix freedom, word lengths and "
                        + "each depth budget, and turns the optimizing path masses into iid masses "
                        + "for p. The iid greedy maximum therefore bounds every finite history "
                        + "truncation. Suprema of the nonnegative finite sums give the infinite "
                        + "bound. Its actual attainment uses the fixed iid process p and the same G; "
                        + "the auxiliary finite optimizers need not agree across horizons. The root "
                        + "budget theorem for finite prefix antichains bounds every finite selection "
                        + "of codewords; the supremum of these sums is at most one.")),
                    Paragraph(Text("The complementary optimum Gamma is one minus sup J, hence one "
                        + "minus S(p,G). At delta = 1/d every admissible row is uniform and p is uniform. "
                        + "Depth zero, empty codes, zero budgets, skipped depths and frontier exhaustion "
                        + "remain included. Constraints depending on letter labels would require an "
                        + "additional invariance hypothesis and are outside this budget class.")),
                    Paragraph(Text("When delta < 1/d, put c = 1 - d times delta. Every admissible row is "
                        + "the convex combination of the extreme rows indexed by their heavy letter, "
                        + "with weights (q(h,a)-delta)/c. These weights are nonnegative, sum to one "
                        + "and reconstruct every coordinate of the original row."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S0/Computability/Coding/HistoryTreeRelabeling")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/History/FinitePrefixAntichainBudget"))]));

    private static Formula MainFormula()
    {
        Formula delta = F.Id("delta"), d = F.Id("d"), b = F.Id("b"), tie = F.Id("tie");
        Formula basis = F.Id("base");
        Formula p = F.Id("p"), g = F.Id("G"), q = F.Id("q"), code = F.Id("F");
        Formula n = F.Id("N"), j = F.Id("J"), a = F.Id("a"), h = F.Id("h");
        Formula finite = F.Seq(Open, Forall, Sp, q, Comma, Sp, Call("Admissible", delta, q),
            Sp, Rightarrow, Sp, Forall, Sp, code, Comma, Sp, Call("Legal", b, code),
            Sp, Rightarrow, Sp, Forall, Sp, n, Comma, Sp, Call("T", q, code, n),
            Sp, Le, Sp, Call("T", p, g, n), Close);
        Formula uniform = F.Seq(Open, delta, Sp, Eq, Sp, F.Seq(D(1), Slash, d),
            Sp, Rightarrow, Sp, Open, Forall, Sp, a, Comma, Sp,
            Call("p", a), Sp, Eq, Sp, delta, Close, Sp, Land, Sp,
            Forall, Sp, q, Comma, Sp, Call("Admissible", delta, q), Sp, Rightarrow, Sp,
            Forall, Sp, h, Comma, Sp, a, Comma, Sp, Call("q", h, a), Sp, Eq, Sp, delta, Close);
        return Disp(F.Seq(Forall, Sp, delta, Comma, Sp, basis, Comma, Sp, b, Comma, Sp, tie, Comma, Sp,
            D(2), Sp, Le, Sp, d, Sp, Land, Sp, D(0), Sp, Lt, Sp, delta, Sp, Land, Sp, d, Sp, delta, Sp, Le, Sp, D(1),
            Sp, Rightarrow, Sp, Call("Legal", b, g), Sp, Land, Sp,
            Call("Admissible", delta, Call("iid", p)), Sp, Land, Sp, finite, Sp, Land, Sp,
            Call("IsGreatest", j, Call("S", p, g)), Sp, Land, Sp,
            Call("sup", j), Sp, Eq, Sp, Call("S", p, g), Sp, Land, Sp,
            Call("S", p, g), Sp, Le, Sp, D(1), Sp, Land, Sp,
            Call("Gamma", d, delta, b), Sp, Eq, Sp, D(1), Sp, Minus, Sp, Call("S", p, g),
            Sp, Land, Sp, Call("S", Call("iid", p), g), Sp, Eq, Sp, Call("S", p, g),
            Sp, Land, Sp, uniform, Dot));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
