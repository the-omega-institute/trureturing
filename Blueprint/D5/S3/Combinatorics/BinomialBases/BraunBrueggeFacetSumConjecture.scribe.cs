using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

internal sealed class BraunBrueggeFacetSumConjectureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/BinomialBases/BraunBrueggeFacetSumConjecture.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/braunbruegge2023facetsymmetricedgepolytope");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Braun–Bruegge's symmetric edge-polytope facet-sum conjecture",
        H("Braun–Bruegge Conjecture 5.1"),
        Blocks(
            Describe.Lean(DescribeId.Create("facet-sum"), DeclarationHandle.Create(Prefix + "F"),
                H("The facet sum"), StatementSource.FromAuthor(Disp(FFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Proposition 4.4 states verbatim: “If all the m_i's have the same parity, N(CB(m)) is given by F(m) = Σ_{j=0}^{m_t} C(m_t, j) [Π_{k=1}^{t−1} C(m_k, (m_k − m_t)/2 + j)].” The displayed Lean expression is its t=3 specialization, with Nat.choose and natural floor division."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("admissible-domain"), DeclarationHandle.Create(Prefix + "Admissible"),
                H("The sorted common-parity domain"), StatementSource.FromAuthor(Disp(AdmissibleFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The source orders the entries so that a≥b≥c, requires positive entries, and requires common parity. The conjunction records exactly those conditions."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("conjecture-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Conjecture 5.1"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Conjecture 5.1 states verbatim: “For n = 2k and k ≥ 2 with x_1 + x_2 + x_3 = n + 1, F(x_1, x_2, x_3) is maximized at F(n − 1, 1, 1). For n = 2k − 1 and k ≥ 3 with x_1 + x_2 + x_3 = n + 1, F(x_1, x_2, x_3) is maximized at F(n − 3, 2, 2). Further, for any x_1 ≥ x_2 ≥ x_3 ≥ 3 all even or all odd positive integers, F(x_1, x_2, x_3) ≤ F(x_1 + 2, x_2, x_3 − 2) and F(x_1, x_2, x_3) ≤ F(x_1 + 2, x_2 − 2, x_3), when the subtraction by 2 will maintain the inequalities on the x_i's.” The four conjuncts encode these assertions with the admissible domain and the stated endpoint conditions."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("conjecture-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The four assertions hold"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The proof writes each facet sum as a weighted sum of centered binomial rows. A Vandermonde identity preserves the paired mass under each two-unit transfer. The transfer difference has one sign crossing, and the third centered row is antitone with distance from the center, so the weighted difference is nonnegative. Strong induction then reaches the endpoint triples in both parity classes. Finite computation checks 58,088 admissible triples for 4≤n≤200; the centered-row argument proves the inequalities for arbitrary admissible triples."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("braun-bruegge-2022-symmetric-edge-polytope-facet-sum-conjecture-5-1"),
                    ResolutionKind.Proved)))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Qualified(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(V(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Local(string name) => Qualified("D5", "S3", "Combinatorics", "BinomialBases", "BraunBrueggeFacetSumConjecture", name);
    private static Formula LC(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Div(Formula left, Formula right) => At(Qualified("Nat", "div"), left, right);
    private static Formula Mod(Formula left, Formula right) => At(Qualified("Nat", "mod"), left, right);
    private static Formula Choose(Formula left, Formula right) => At(Qualified("Nat", "choose"), left, right);
    private static Formula Range(Formula upper) => At(Qualified("Finset", "range"), upper);
    private static Formula SumFormula(string variable, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Member(V(variable), domain)), Sp, Parenthesized(body));
    private static Formula FCall(Formula a, Formula b, Formula c) => LC("F", a, b, c);
    private static Formula AdCall(Formula a, Formula b, Formula c) => LC("Admissible", a, b, c);

    private static Formula FFormula()
    {
        var a = V("a"); var b = V("b"); var c = V("c"); var j = V("j");
        var body = Mul(Mul(Choose(c, j), Choose(b, Add(Div(Sub(b, c), D(2)), j))), Choose(a, Add(Div(Sub(a, c), D(2)), j)));
        return All("a", Nat(), All("b", Nat(), All("c", Nat(), Eq(FCall(a, b, c), SumFormula("j", Range(Add(c, D(1))), body)))));
    }

    private static Formula AdmissibleFormula()
    {
        var a = V("a"); var b = V("b"); var c = V("c");
        var body = And(Le(b, a), And(Le(c, b), And(Le(D(1), c), And(Eq(Mod(a, D(2)), Mod(b, D(2))), Eq(Mod(b, D(2)), Mod(c, D(2)))))));
        return All("a", Nat(), All("b", Nat(), All("c", Nat(), Iff(AdCall(a, b, c), body))));
    }

    private static Formula ClaimBody()
    {
        var a = V("a");
        var b = V("b");
        var c = V("c");
        var k = V("k");

        var firstConclusion = Le(
            FCall(a, b, c),
            FCall(Sub(Mul(D(2), k), D(1)), D(1), D(1)));
        var firstSum = Eq(
            Add(Add(a, b), c),
            Add(Mul(D(2), k), D(1)));
        var first = All("k", Nat(),
            Imp(Le(D(2), k),
                All("a", Nat(),
                    All("b", Nat(),
                        All("c", Nat(),
                            Imp(AdCall(a, b, c),
                                Imp(firstSum, firstConclusion)))))));

        var secondConclusion = Le(
            FCall(a, b, c),
            FCall(Sub(Sub(Mul(D(2), k), D(1)), D(3)), D(2), D(2)));
        var secondSum = Eq(
            Add(Add(a, b), c),
            Add(Sub(Mul(D(2), k), D(1)), D(1)));
        var second = All("k", Nat(),
            Imp(Le(D(3), k),
                All("a", Nat(),
                    All("b", Nat(),
                        All("c", Nat(),
                            Imp(AdCall(a, b, c),
                                Imp(secondSum, secondConclusion)))))));

        var thirdConclusion = Le(
            FCall(a, b, c),
            FCall(Add(a, D(2)), b, Sub(c, D(2))));
        var third = All("a", Nat(),
            All("b", Nat(),
                All("c", Nat(),
                    Imp(AdCall(a, b, c),
                        Imp(Le(D(3), c), thirdConclusion)))));

        var fourthConclusion = Le(
            FCall(a, b, c),
            FCall(Add(a, D(2)), Sub(b, D(2)), c));
        var fourth = All("a", Nat(),
            All("b", Nat(),
                All("c", Nat(),
                    Imp(AdCall(a, b, c),
                        Imp(Le(D(3), c),
                            Imp(Le(c, Sub(b, D(2))), fourthConclusion))))));
        return And(first, And(second, And(third, fourth)));
    }
}
