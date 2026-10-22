using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Coding;

internal sealed class BiasedMassFrontierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First threshold crossings partition the biased binary boundary with exact total mass.",
        H("First Mass Crossings in a Biased Binary Tree"),
        Blocks(
            Paragraph(Text(
                "Let a and b be real letter probabilities with 0 < b <= a < 1 and a + b = 1. "
                + "The alphabet is Bool: false has mass a and true has mass b. The function "
                + "letterMass supplies these probabilities to wordMass, the product over the actual "
                + "letters of a finite word. The empty word has mass one. Write m(w) for this "
                + "product and parent(w) for the word obtained by deleting its last letter.")),
            Paragraph(Text(
                "For 0 < t < 1, Crossing(a,b,t) consists exactly of the nonempty words w with "
                + "m(w) <= t < m(parent(w)). Equality at the lower threshold is a stopping event. "
                + "A ray is any function from the natural numbers to Bool; rayPrefix(r,n) is its "
                + "first n letters. A word is a prefix of r precisely when w = rayPrefix(r,length(w)).")),
            Describe.Lean(
                DescribeId.Create("biased-first-mass-frontier"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/BiasedMassFrontier.biased_first_mass_frontier"),
                H("A finite conservative frontier with reciprocal size bounds"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each letter has mass at most a, so m(w) <= a raised to length(w). Choose "
                        + "a common finite N for which a raised to N is less than t. Starting at "
                        + "the root, stop at a word of mass at most t; otherwise replace it by its "
                        + "two children. Every branch has stopped by N.")),
                    Paragraph(Text(
                        "The two child subtrees are disjoint, and their masses add to their "
                        + "parent mass because a + b = 1. Induction on the finite remaining depth "
                        + "therefore preserves total mass exactly. Mass decreases under extension, "
                        + "so two first-crossing words cannot properly extend one another. Extending "
                        + "any word to depth N identifies the recursive leaves with the entire "
                        + "crossing set, and each infinite ray meets exactly one leaf.")),
                    Paragraph(Text(
                        "At a crossing the parent mass is strictly greater than t and the last "
                        + "letter has mass at least b. Thus b times t is strictly less than each "
                        + "leaf mass, while every leaf mass is at most t. Summing these inequalities "
                        + "and using the conserved mass one gives the displayed cardinality bounds. "
                        + "The equal-probability case and thresholds equal to a word mass are included."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality"))]));

    private static Formula MainFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), t = F.Id("t");
        Formula n = F.Id("N"), frontier = F.Id("A"), w = F.Id("w"), r = F.Id("r");
        Formula m = Call("m", w), card = Call("card", frontier);
        Formula bt = F.Seq(b, Sp, t);
        Formula assumptions = F.Seq(
            D(0), Sp, Lt, Sp, b, Sp, Le, Sp, a, Sp, Lt, Sp, D(1), Sp, Land, Sp,
            a, Sp, Plus, Sp, b, Sp, Eq, Sp, D(1), Sp, Land, Sp,
            D(0), Sp, Lt, Sp, t, Sp, Lt, Sp, D(1));
        Formula length = F.Seq(Forall, Sp, w, Sp, InMacro, Sp, frontier, Comma, Sp,
            Call("length", w), Sp, Le, Sp, n);
        Formula ray = F.Seq(Forall, Sp, r, Colon, Sp, F.Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp,
            F.Id("Bool"), Comma, Sp, Exists, Bang, Sp, w, Comma, Sp,
            w, Sp, InMacro, Sp, frontier, Sp, Land, Sp,
            w, Sp, Eq, Sp, Call("rayPrefix", r, Call("length", w)));
        Formula total = F.Seq(Sum, Underscore, Grp(w, Sp, InMacro, Sp,
            frontier), Sp, m, Sp, Eq, Sp, D(1));
        Formula leaf = F.Seq(Forall, Sp, w, Sp, InMacro, Sp, frontier, Comma, Sp,
            bt, Sp, Lt, Sp, m, Sp, Le, Sp, t);
        Formula count = F.Seq(F.Seq(Frac, Grp(D(1)), Grp(t)), Sp, Le, Sp, card, Sp, Lt, Sp, F.Seq(Frac, Grp(D(1)), Grp(bt)));
        return Disp(F.Seq(Forall, Sp, a, Comma, Sp, b, Comma, Sp, t, Sp, InMacro, Sp,
            F.Seq(Mathbb, Grp(F.Id("R"))), Comma, Sp, assumptions, Sp, Rightarrow, Sp,
            Exists, Sp, n, Sp, InMacro, Sp, F.Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
            Exists, Sp, frontier, Colon, Sp, Call("Finset", Call("List", F.Id("Bool"))), Comma, Sp,
            frontier, Sp, Eq, Sp, Call("Crossing", a, b, t), Sp, Land, Sp,
            Open, length, Close, Sp, Land, Sp, Call("IsPrefixFree", frontier), Sp, Land, Sp,
            Open, ray, Close, Sp, Land, Sp, total, Sp, Land, Sp,
            Open, leaf, Close, Sp, Land, Sp, count));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
