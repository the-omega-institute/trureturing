using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class FernauRystsovIntermediateResetDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/fernau2026shortest");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two finite chains over a shared binary alphabet realize every product reset threshold between the maximum and the sum of their factor thresholds.",
        H("Every intermediate reset threshold occurs in a DFA product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("threshold"),
                DeclarationHandle.Create("D5/S0/Automata/FernauRystsovIntermediateReset.Threshold"),
                H("Minimum observed reset length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For any state type σ, a total DFA M over Bool, a function ℓ from finite Boolean words to natural numbers and a natural number n, Threshold ℓ M n asserts that there exists a word w with ℓ(w) = n and singleton full-state image under evaluation. Every finite word v with singleton full-state image must satisfy n ≤ ℓ(v). The function ℓ is a parameter, and the attainment theorem instantiates it with List.length. The definition quantifies over the empty word as well."))),
                DescribeRole.Definition),
            Describe.Lean(
            DescribeId.Create("intermediate-reset-thresholds"),
            DeclarationHandle.Create("D5/S0/Automata/FernauRystsovIntermediateReset.result"),
            H("Attainment throughout the product interval"),
            StatementSource.FromAuthor(Attainment()),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text("The second bullet of §7, p. 19, asks “"
                    + "Can we show that each “intermediate number” between the lower and upper bound of Proposition 7 can be attained?”")),
                Paragraph(Text("Write T(M,n) when some finite word of length n maps the entire state set of M to a singleton, and every word with singleton full-state image has length at least n. "
                    + "Words include the empty word. Both automata have total transitions and use Bool, with a = false and b = true. "
                    + "Their state sets are Fin(r+1) and Fin(s+1), which are nonempty even at threshold zero. "
                    + "The product A × B acts on the full Cartesian state set by applying the same letter in both coordinates. "
                    + "The designated start and accepting states play no role in the full-state reset test.")),
                Paragraph(Text("Put t = r+s−m, so 0 ≤ t ≤ min(r,s). In the first chain, a advances one step up to r, and b advances one step only below t. "
                    + "In the second chain, a fixes every state and b advances one step up to s. The factor reset words are r copies of a and s copies of b. "
                    + "No shorter word can take the bottom to the fixed top in either factor because each coordinate advances by at most one per letter.")),
                Paragraph(Text("In the product, s copies of b bring every first coordinate to at least t and every second coordinate to s. "
                    + "Then r−t copies of a finish the first coordinate while fixing the second. "
                    + "Any reset word must send (0,0) to the fixed pair (r,s). The potential max(i−t,0)+j increases by at most one per letter. "
                    + "Letter a can increase only the first summand, and letter b leaves the first summand unchanged while advancing the second coordinate. "
                    + "The total increase from (0,0) to (r,s) is m, which proves minimality over all words.")),
                Paragraph(Text("The lower endpoint has t = min(r,s) and the upper endpoint has t = 0. "
                    + "A zero factor threshold gives a singleton with the empty reset word, and m then equals the other threshold. "
                    + "Proposition 7 supplies the necessity of the interval for finite factor and product thresholds."))),
            DescribeRole.Theorem,
            openProblemResolutionClaim: new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("fernau-rystsov-2026-intermediate-reset-thresholds"),
                ResolutionKind.Proved)))));

    private static Formula Attainment()
    {
        Formula r = F.Id("r"), s = F.Id("s"), m = F.Id("m");
        Formula a = F.Id("A"), b = F.Id("B");
        var nat = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        var low = new Formula.Relation(Call("max", r, s), FormulaRelationOperator.LessThanOrEqual, m);
        var high = new Formula.Relation(m, FormulaRelationOperator.LessThanOrEqual, Add(r, s));
        var product = F.Seq(a, F.Sp, F.Times, F.Sp, b);
        return F.Disp(new Formula.Aligned([
            F.Seq(Binder(F.Forall, F.Seq(r, F.Comma, s, F.Comma, m), nat),
                F.Open, And(low, high), F.Close, F.Sp, F.Longrightarrow),
            F.Seq(Binder(F.Exists, a, Automaton(r)), Binder(F.Exists, b, Automaton(s)),
                And(Call("T", a, r), And(Call("T", b, s), Call("T", product, m)))),
        ]));
    }

    private static Formula Automaton(Formula threshold) =>
        Call("DFA", F.Seq(F.Mathrm, F.Grp(F.Id("Bool"))), Call("Fin", Add(threshold, F.D(1))));

    private static Formula Binder(Formula quantifier, Formula variable, Formula type) =>
        F.Seq(quantifier, F.Sp, variable, F.Colon, F.Sp, type, F.Comma, F.Sp);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Call(string function, params Formula[] args) =>
        new Formula.Apply(F.Seq(F.Operatorname, F.Grp(F.Id(function))), [.. args]);
}
