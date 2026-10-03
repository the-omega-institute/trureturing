using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.CayleyGrowth;

internal sealed class ConsecutiveFourCycleDiameterRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/CayleyGrowth/chervov2026cayleypy4");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjecture 11 of CayleyPy-4 fails at n = 6: reversal cannot be reached in four "
            + "consecutive-four-cycle moves, while the proposed diameter is four.",
        H("Consecutive four-cycle diameter refutation"),
        Blocks(
            Node("cycle", "Nonwrapped consecutive four-cycle",
                "The permutation of Fin n sends i to i + 1, i + 1 to i + 2, i + 2 to "
                    + "i + 3, and i + 3 to i, fixing every other point. The starting index "
                    + "satisfies i + 4 <= n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("generators", "Inverse-closed generators",
                "The generating set contains all these cycles and their inverses. "
                    + "The indices run from zero through n - 4; no cycle wraps around.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("graph", "Cayley graph on the full symmetric group",
                "Vertices are permutations of Fin n. Two distinct vertices u and v are "
                    + "adjacent when u times a generator equals v, or v times a generator "
                    + "equals u. Inverse closure identifies both alternatives with a "
                    + "single generator move. The diameter ediam takes values in the "
                    + "extended naturals, with infinity reserved for unbounded distances.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("formula", "The proposed rational diameter",
                "Write F(n) for n(n - 1)/6 + 2/3 when n has residue two modulo three, "
                    + "and n(n - 1)/6 - 1 when its residue is zero or one. All subtraction "
                    + "and division in this formula take place in the rationals.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("consecutive-four-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The complete k = 4 clause of Conjecture 11"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every n >= 6 the diameter must be finite and equal to F(n). "
                        + "The notation castENat embeds a natural into the extended naturals, "
                        + "and castRat embeds it into the rationals."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("consecutive-four-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Refutation of the complete universal clause"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "At n = 6 the six generators are (0123), (1234), (2345) and their "
                        + "inverses. Starting with the identity, repeatedly retain the current "
                        + "products and append each product times each generator. After four "
                        + "iterations the reversal (05)(14)(23) is absent. Induction on graph "
                        + "walks shows that a walk of length at most four from the identity "
                        + "ends among these products, including when an edge is expressed "
                        + "in reverse. The formula gives F(6) = 4. A diameter of four would "
                        + "bound the distance to reversal by four, and a shortest walk would "
                        + "then contradict its exclusion. This establishes falsity of the "
                        + "entire k = 4 clause; it does not determine the exact diameter or "
                        + "a corrected formula. Theorem 5 of the same paper already supplies "
                        + "a sufficient lower bound, so the bound and method are not new."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chervov-2026-cayleypy4-conjecture-eleven-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("consecutive-four-" + name), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula All(string variable, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable),
        Seq(Mathbb, Grp(F.Id("N"))), body);
    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d");
        Formula diameter = Equal(Call("ediam", Call("graph", n)), Call("castENat", d));
        Formula value = Equal(Call("castRat", d), Call("formula", n));
        Formula exists = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("d"),
            Seq(Mathbb, Grp(F.Id("N"))), new Formula.Logic(diameter, FormulaLogicOperator.And, value));
        Formula threshold = new Formula.Relation(D(6), FormulaRelationOperator.LessThanOrEqual, n);
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            All("n", new Formula.Logic(threshold, FormulaLogicOperator.Implies, exists))));
    }
}
