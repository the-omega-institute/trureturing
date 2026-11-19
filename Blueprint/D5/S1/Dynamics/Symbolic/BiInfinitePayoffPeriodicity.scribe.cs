using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class BiInfinitePayoffPeriodicityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/BiInfinitePayoffPeriodicity.";
    private static readonly Formula Z = new Formula.Integers();
    private static readonly Formula N = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula R = Seq(Mathbb, Grp(F.Id("R")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded irrational discrepancy excludes repetition, and finite two-sided edge presentations yield periodic points.",
        H("Periodicity Tests for Two-Sided Payoff Shifts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bounded-irrational-discrepancy"),
                DeclarationHandle.Create(Owner + "no_positive_period_of_irrational_discrepancy"),
                H("Bounded discrepancy excludes a positive period"),
                StatementSource.FromAuthor(Disp(DiscrepancyObstruction())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text(
                    "Here D(a, α, i, n) is the number of true letters of a at coordinates i through "
                    + "i + n − 1 minus nα. For a positive period p containing c true letters, a window "
                    + "of k periods has discrepancy k(c − pα). Irrationality makes its absolute value "
                    + "exceed seven for large enough k."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cycle-in-finite-edge-presentation"),
                DeclarationHandle.Create(Owner + "exists_periodic_point_of_finite_edge_presentation"),
                H("A nonempty finite edge presentation yields a periodic point"),
                StatementSource.FromAuthor(Disp(PeriodicPoint())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text(
                    "The finite vertex and edge types and the alphabet can lie in arbitrary universes. "
                    + "Presented means that for every integer-indexed alphabet point, membership is "
                    + "equivalent to the existence of an integer-indexed edge walk whose target at "
                    + "each index is the source at its successor and whose label is the point at that index. "
                    + "A repeated vertex on the nonnegative ray gives a positive-length closed edge walk. "
                    + "Remainders modulo its length extend that walk over all integers, including its seam."))),
                DescribeRole.Theorem))));

    private static Formula DiscrepancyObstruction()
    {
        var a = F.Id("a");
        var i = F.Id("i");
        var n = F.Id("n");
        var p = F.Id("p");
        var bound = All(i, Z, All(n, N, ImpliesOf(AtMost(D(2), n),
            AtMost(new Formula.Absolute(Apply("D", a, Alpha, i, n)), D(7)))));
        return All(a, new Formula.TypeArrow(Z, F.Id("Bool")), All(Alpha, R,
            ImpliesOf(Apply("Irrational", Alpha), ImpliesOf(bound,
                new Formula.Not(Parens(ExistsOf(p, Z, And(Less(D(0), p), Apply("Periodic", a, p)))))))));
    }

    private static Formula PeriodicPoint()
    {
        var v = F.Id("V");
        var e = F.Id("E");
        var a = F.Id("A");
        var s = F.Id("s");
        var t = F.Id("t");
        var l = F.Id("l");
        var y = F.Id("Y");
        var x = F.Id("x");
        var p = F.Id("p");
        var configuration = new Formula.TypeArrow(Z, a);
        var member = Seq(x, Sp, InMacro, Sp, y);
        var result = ExistsOf(x, configuration,
            And(member, ExistsOf(p, Z, And(Less(D(0), p), Apply("Periodic", x, p)))));
        var statement = All(s, new Formula.TypeArrow(e, v), All(t, new Formula.TypeArrow(e, v),
            All(l, new Formula.TypeArrow(e, a), All(y, Apply("Set", Parens(configuration)),
                ImpliesOf(Apply("Presented", s, t, l, y), ImpliesOf(Apply("Nonempty", y), result))))));
        return All(v, F.Id("Type"), All(e, F.Id("Type"), All(a, F.Id("Type"),
            Seq(OpenBracket, Apply("Finite", v), CloseBracket, Sp,
                OpenBracket, Apply("Finite", e), CloseBracket, Comma, Sp, statement))));
    }

    private static Formula Apply(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Parens(Formula value) => Seq(Open, value, Close);
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, Parens(Seq(variable, Colon, Sp, domain)), Comma, Sp, body);
    private static Formula ExistsOf(Formula variable, Formula domain, Formula body) =>
        Seq(Exists, Sp, Parens(Seq(variable, Colon, Sp, domain)), Comma, Sp, body);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula ImpliesOf(Formula left, Formula right) =>
        new Formula.Logic(Parens(left), FormulaLogicOperator.Implies, Parens(right));
}
