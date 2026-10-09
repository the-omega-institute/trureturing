using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Coding;

internal sealed class BudgetMarginNoncomputabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite support without a supplied endpoint does not make budget optimization uniform.",
        H("Budget Programs without Effective Tails"),
        Blocks(
            Paragraph(Text(
                "Fix a natural alphabet size d at least two and the uniform iid probability "
                + "vector p(a)=1/d on Fin(d). Legal(b,F) is the prefix-code condition: F excludes "
                + "the empty word and has at most b(n) words of each length n. Its deleted mass "
                + "is the nonnegative sum of the iid word masses. The real quantity optimalMass(d,b) "
                + "is the real part of the supremum of these masses over the same legal codes; "
                + "the frozen greedy optimum attains this supremum. The surviving margin is "
                + "margin(d,b)=1-optimalMass(d,b).")),
            Paragraph(Text(
                "The input e is a partial-recursive program code. Presents(e,b) means that "
                + "evaluation of e on every natural n terminates with exactly b(n). Promise(d,e,b) "
                + "requires this presentation, finite support of b, b(0)=0, subexponential growth, "
                + "and budgetSum(d,b)<1. Here budgetSum is the sum of b(n)/d^n over all natural n, "
                + "and subexponential growth means that for every real a>1 there is a natural N "
                + "such that b(n) is at most a^n for all n at least N. The endpoint of the support "
                + "and the growth thresholds are semantic promises, not additional input data.")),
            Paragraph(Text(
                "MarginSelector(d,A) requires partial recursiveness of A from codes to pairs "
                + "of naturals. For every e and b satisfying Promise(d,e,b), A(e) must terminate "
                + "with a pair (u,v) whose positive rational (u+1)/(v+1) is at most margin(d,b). "
                + "Every positive rational has such a representation. Termination outside the "
                + "promise is unrestricted, and different indices of the same budget may yield "
                + "different answers.")),
            Paragraph(Text(
                "CauchySelector(d,A) requires a partial recursive operator on budget codes. It "
                + "returns a name program q. At every precision k, that program returns an "
                + "encoded triple of naturals. "
                + "For every promised e,b and every natural precision k, "
                + "the query must terminate with (u,v,w) such that the signed rational "
                + "(u-v)/(w+1) differs from optimalMass(d,b) by at most 2^(-k). This encoding "
                + "allows every rational number. No condition is imposed on queries outside "
                + "the promise.")),
            Describe.Lean(
                DescribeId.Create("budget-margin-noncomputability"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/BudgetMarginNoncomputability.result"),
                H("Neither a positive margin nor a Cauchy name can be extracted uniformly"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Bounded universal evaluation gives, uniformly from any source code c, "
                        + "a total budget program. At the first positive evaluation stage n that "
                        + "detects halting on input zero, its budget is d^n-1; all other entries "
                        + "are zero. If the source never halts, every entry is zero. Thus every "
                        + "source yields a promised budget, without deciding whether it halts.")),
                    Paragraph(Text(
                        "For a first event at n, only words at depth n are legal, and exactly "
                        + "d^n-1 words can be selected. Each has uniform mass d^(-n). The optimal "
                        + "deleted mass is therefore 1-d^(-n), with surviving margin d^(-n). "
                        + "For a nonhalting source, the optimum is zero and the margin is one.")),
                    Paragraph(Text(
                        "A positive-margin output provides a finite bound on every possible "
                        + "first halting stage. Finite simulation through that bound then decides "
                        + "halting for all source codes. A Cauchy output at precision three instead "
                        + "separates zero optimal mass from optimal mass at least one half by the "
                        + "threshold one quarter. Both contradict undecidability of halting. "
                        + "Since finite-support budgets form a subdomain of the original growth "
                        + "promise, either proposed algorithm on that larger domain is excluded too."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality"))]));

    private static Formula MainFormula()
    {
        Formula d = F.Id("d"), a = F.Id("A");
        Formula margin = F.Seq(Neg, Sp, Exists, Sp, a, Comma, Sp,
            Call("MarginSelector", d, a));
        Formula cauchy = F.Seq(Neg, Sp, Exists, Sp, a, Comma, Sp,
            Call("CauchySelector", d, a));
        return Disp(F.Seq(Forall, Sp, d, Sp, InMacro, Sp, F.Grp(Mathbb, F.Grp(F.Id("N"))), Comma, Sp,
            D(2), Sp, Le, Sp, d, Sp, Rightarrow, Sp,
            Open, margin, Close, Sp, Land, Sp, Open, cauchy, Close));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
