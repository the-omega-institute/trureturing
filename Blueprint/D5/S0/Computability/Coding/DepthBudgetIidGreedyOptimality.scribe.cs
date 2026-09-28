using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Coding;

internal sealed class DepthBudgetIidGreedyOptimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One iid greedy prefix code maximizes every finite truncation and the total mass.",
        H("Greedy Prefix Codes with Arbitrary Depth Budgets"),
        Blocks(
            Paragraph(Text(
                "Let A be a finite alphabet, p a strictly positive real probability vector on A, "
                + "and b an arbitrary natural-valued function on depths. A word has mass equal to "
                + "the product of p over its letters. At each depth fix a total "
                + "tie order on words. Priority first compares iid word mass in decreasing order "
                + "and then the fixed tie order. No computability assumption is imposed on p.")),
            Paragraph(Text(
                "Start with the empty word as the live frontier. Extend every live word by every "
                + "letter, select the first min(b(n), live count) words in priority order at the "
                + "positive depth n, and continue from the remaining frontier. The union G of all "
                + "selected words is defined by this single recursion, without a terminal depth. "
                + "Thus o(n) = priority(p,tie(n)) and G = greedyCode(o,b).")),
            Paragraph(Text(
                "Legal(b,F) means that F is prefix-free, excludes the empty word and contains at "
                + "most b(n) distinct words of each length n. Write T(p,F,N) for the sum of iid "
                + "masses of words of F of length at most N, and S(p,F) for the nonnegative "
                + "countable sum over all words of F. The latter is represented in the extended "
                + "nonnegative reals. IsGreatest asserts membership and an upper bound for every "
                + "member of the displayed set. The condition depthAtMost(F,N) means that every word "
                + "of F has length at most N.")),
            Describe.Lean(
                DescribeId.Create("depth-budget-iid-greedy-optimality"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality.depth_budget_iid_greedy_optimality"),
                H("One code attains all finite maxima and the infinite supremum"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each mass threshold, the greedy live frontier has no more words "
                        + "above that threshold than any competitor. Iid expansion preserves this "
                        + "comparison by summing over letters. Removing the heaviest permitted "
                        + "words preserves it under any competing deletion within the same budget.")),
                    Paragraph(Text(
                        "Hall's marriage theorem converts threshold domination into an injective "
                        + "matching with no smaller masses on the competitor side. Conservation "
                        + "of live mass plus deleted mass gives finite optimality. Prefix freedom "
                        + "identifies the recursive competitor frontier with the words having no "
                        + "selected ancestor. Suprema of nonnegative finite sums give the infinite "
                        + "conclusion for the same G.")),
                    Paragraph(Text(
                        "Depth zero, zero budgets, skipped depths, saturation and permanently "
                        + "empty frontiers are included. No summable budget tail, compactness or "
                        + "continuity of the objective is required. The result also allows a "
                        + "singleton alphabet; in particular it applies when A has at least two letters."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/Coding/PrefixFreeCode"))]));

    private static Formula MainFormula()
    {
        Formula p = F.Id("p"), b = F.Id("b"), tie = F.Id("tie");
        Formula a = F.Id("a"), n = F.Id("N"), x = F.Id("x");
        Formula code = F.Id("F"), greedy = F.Id("G");
        Formula legal = Call("Legal", b, code);
        Formula finiteSet = F.Seq(OpenBrace, x, Sp, Mid, Sp, Exists, Sp, code, Comma, Sp,
            legal, Sp, Land, Sp, Call("depthAtMost", code, n), Sp, Land, Sp,
            x, Sp, Eq, Sp, Call("T", p, code, n), CloseBrace);
        Formula totalSet = F.Seq(OpenBrace, x, Sp, Mid, Sp, Exists, Sp, code, Comma, Sp,
            legal, Sp, Land, Sp, x, Sp, Eq, Sp, Call("S", p, code), CloseBrace);
        Formula finite = F.Seq(Forall, Sp, n, Comma, Sp,
            Call("IsGreatest", finiteSet, Call("T", p, greedy, n)));
        Formula total = Call("IsGreatest", totalSet, Call("S", p, greedy));
        Formula assumptions = F.Seq(Open, Forall, Sp, a, Comma, Sp,
            D(0), Sp, Lt, Sp, Call("p", a), Close, Sp, Land, Sp,
            Sum, Underscore, a, Sp, Call("p", a), Sp, Eq, Sp, D(1));
        return Disp(F.Seq(Forall, Sp, p, Comma, Sp, b, Comma, Sp, tie, Comma, Sp,
            assumptions, Sp, Rightarrow, Sp,
            Call("Legal", b, greedy), Sp, Land, Sp, Open, finite, Close,
            Sp, Land, Sp, total, Dot));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
