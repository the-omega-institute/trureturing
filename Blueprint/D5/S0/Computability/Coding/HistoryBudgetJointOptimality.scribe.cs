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
                + "the iid truncatedMass(p,F,N), and the countable iid codeMass(p,F) are the existing "
                + "prefix-code constructions. The history versions replace iid products with actual "
                + "conditional path products. J is the set of all historyCodeMass(q,F) with q admissible and F legal. "
                + "Countable masses and their supremum lie in the extended nonnegative reals and are at most one. "
                + "The formula uses d for the alphabet cardinality and toReal for the real value of an "
                + "extended nonnegative mass. Event mass is represented by the sum of path masses "
                + "over a prefix code. No measure on infinite paths is constructed here, and equality "
                + "with the measure of the union of cylinders is not formalized.")),
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
                    Paragraph(Text("Both the extended nonnegative complement and the real complement are one "
                        + "minus the corresponding optimum, hence one minus the corresponding value "
                        + "of codeMass(p,G). At delta = 1/d every admissible row is uniform and p is uniform. "
                        + "Depth zero, empty codes, zero budgets, skipped depths and frontier exhaustion "
                        + "remain included. Constraints depending on letter labels would require an "
                        + "additional invariance hypothesis and are outside this budget class.")),
                    Paragraph(Text("When delta < 1/d, put c = 1 - d times delta. Every admissible row is "
                        + "the convex combination of the extreme rows indexed by their heavy letter, "
                        + "with weights (q(h,a)-delta)/c. These weights are nonnegative, sum to one "
                        + "and reconstruct every coordinate of the original row.")),
                    Paragraph(Text("A method precedent is the finite dice model and finite-event Bellman "
                        + "recursion in Beigi-Etesami-Gohari, Deterministic Randomness Extraction from "
                        + "Generalized and Distributed Santha-Vazirani Sources, arXiv:1412.6641v1, "
                        + "Definition 1 and Theorem 6, as cited in source Section 6.99. Its finite-event "
                        + "result supplies a method precedent for the recursion, while the infinite "
                        + "budget conclusion follows from the path-sum argument here."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S0/Computability/Coding/HistoryTreeRelabeling")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/History/FinitePrefixAntichainBudget")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality"))]));

    private static Formula MainFormula()
    {
        Formula delta = F.Id("delta"), d = F.Id("d"), b = F.Id("b"), tie = F.Id("tie");
        Formula basis = F.Id("base");
        Formula p = F.Id("p"), g = F.Id("G"), q = F.Id("q"), code = F.Id("F");
        Formula n = F.Id("N"), j = F.Id("J"), a = F.Id("a"), h = F.Id("h");
        Formula heavy = F.Id("heavy"), c = F.Id("c"), x = F.Id("x");
        Formula iid = F.Seq(Open, h, Sp, Mapsto, Sp, p, Close);
        Formula mass = Call("codeMass", p, g), sup = Call("sSup", j);
        Formula weight = F.Seq(Open, Call("q", h, a), Sp, Minus, Sp, delta, Close, Slash, c);
        Formula heavyWeight = F.Seq(Open, Call("q", h, heavy), Sp, Minus, Sp, delta, Close, Slash, c);
        Formula finite = F.Seq(Open, Forall, Sp, q, Comma, Sp, Call("Admissible", delta, q),
            Sp, Rightarrow, Sp, Forall, Sp, code, Comma, Sp, Call("Legal", b, code),
            Sp, Rightarrow, Sp, Forall, Sp, n, Comma, Sp, Call("historyTruncatedMass", q, code, n),
            Sp, Le, Sp, Call("truncatedMass", p, g, n), Close);
        Formula mixture = F.Seq(Open, delta, Sp, Lt, Sp, D(1), Slash, d,
            Sp, Rightarrow, Sp, Forall, Sp, q, Comma, Sp, Call("Admissible", delta, q),
            Sp, Rightarrow, Sp, Forall, Sp, h, Comma, Sp,
            Open, Forall, Sp, a, Comma, Sp, D(0), Sp, Le, Sp, weight, Close,
            Sp, Land, Sp, Sum, Underscore, a, Sp, weight, Sp, Eq, Sp, D(1),
            Sp, Land, Sp, Open, Forall, Sp, a, Comma, Sp, Call("q", h, a), Sp, Eq, Sp,
            Sum, Underscore, heavy, Sp, Open, heavyWeight, Close, Sp,
            Call("extremeRow", delta, heavy, a), Close, Close);
        Formula uniform = F.Seq(Open, delta, Sp, Eq, Sp, D(1), Slash, d,
            Sp, Rightarrow, Sp, Open, Forall, Sp, a, Comma, Sp,
            Call("p", a), Sp, Eq, Sp, delta, Close, Sp, Land, Sp,
            Forall, Sp, q, Comma, Sp, Call("Admissible", delta, q), Sp, Rightarrow, Sp,
            Forall, Sp, h, Comma, Sp, a, Comma, Sp, Call("q", h, a), Sp, Eq, Sp, delta, Close);
        Formula totalSet = F.Seq(OpenBrace, x, Sp, Mid, Sp, Exists, Sp, q, Comma, Sp,
            Call("Admissible", delta, q), Sp, Land, Sp, Exists, Sp, code, Comma, Sp,
            Call("Legal", b, code), Sp, Land, Sp, x, Sp, Eq, Sp,
            Call("historyCodeMass", q, code), CloseBrace);
        Formula order = F.Seq(Open, n, Sp, Mapsto, Sp,
            Call("priority", p, Call("tie", n)), Close);
        return Disp(F.Seq(Forall, Sp, delta, Comma, Sp, basis, Comma, Sp, b, Comma, Sp, tie, Comma, Sp,
            p, Comma, Sp, g, Comma, Sp, j, Comma, Sp, c, Comma, Sp,
            D(2), Sp, Le, Sp, d, Sp, Land, Sp, D(0), Sp, Lt, Sp, delta, Sp, Land, Sp, d, Sp, delta, Sp, Le, Sp, D(1),
            Sp, Rightarrow, Sp, Open,
            p, Sp, Eq, Sp, Call("extremeRow", delta, basis), Sp, Land, Sp,
            g, Sp, Eq, Sp, Call("greedyCode", order, b), Sp, Land, Sp,
            j, Sp, Eq, Sp, totalSet, Sp, Land, Sp,
            c, Sp, Eq, Sp, D(1), Sp, Minus, Sp, d, Sp, delta, Close,
            Sp, Rightarrow, Sp, Call("Legal", b, g), Sp, Land, Sp,
            Call("Admissible", delta, iid), Sp, Land, Sp, finite, Sp, Land, Sp,
            Call("IsGreatest", j, mass), Sp, Land, Sp,
            sup, Sp, Eq, Sp, mass, Sp, Land, Sp, mass, Sp, Le, Sp, D(1), Sp, Land, Sp,
            D(1), Sp, Minus, Sp, sup, Sp, Eq, Sp, D(1), Sp, Minus, Sp, mass, Sp, Land, Sp,
            D(1), Sp, Minus, Sp, Call("toReal", sup), Sp, Eq, Sp,
            D(1), Sp, Minus, Sp, Call("toReal", mass), Sp, Land, Sp,
            Call("historyCodeMass", iid, g), Sp, Eq, Sp, mass,
            Sp, Land, Sp, mixture, Sp, Land, Sp, uniform, Dot));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
