using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class Erdos699AdjacentCoresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent coprime divisibility cores obey a cubic necessary bound.",
        H("Erdos 699 Adjacent-Core Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("erdos699-adjacent-core-numerator-bound"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Erdos699AdjacentCores.adjacent_core_numerator_bound"),
            H("Cubic bound from adjacent cores"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "All variables range over natural numbers, and subtraction is truncated "
                    + "natural subtraction. The assumptions are precisely the displayed "
                    + "positivity, half-range, coprimality, divisibility, defect bounds and "
                    + "two equations for n. No binomial coefficient or Lucas condition is "
                    + "asserted by this theorem.")),
                Paragraph(Text(
                    "Coprimality makes the product of the two cores divide "
                    + "t(M-t)(M-2t). The identity "
                    + "4(M^6-108[t(M-t)(M-2t)]^2)="
                    + "(M^2-3(M-2t)^2)^2(4M^2-3(M-2t)^2) "
                    + "gives the exact polynomial envelope. The defect factors at most three "
                    + "give the stated square bound. This is a necessary-condition lemma "
                    + "for the i=3 reduction; it does not resolve Erdos problem 699."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n"), m = F.Id("M"), t = F.Id("t");
        Formula r1 = F.Id("R1"), r2 = F.Id("R2");
        Formula d1 = F.Id("delta1"), d2 = F.Id("delta2");
        Formula mt = Sub(m, t), m2t = Sub(m, Mul(D(2), t));
        Formula core = Mul(Mul(t, mt), m2t);
        Formula assumptions = And(
            Lt(D(0), t), Lt(Mul(D(2), t), m), Call("Coprime", r1, r2),
            Divides(r1, Mul(t, mt)), Divides(r2, core),
            Le(d1, D(3)), Le(d2, D(3)),
            Eq(n, Add(Mul(d1, r1), D(1))),
            Eq(n, Add(Mul(Mul(D(2), d2), r2), D(2))));
        Formula lhs = Pow(Mul(Sub(n, D(1)), Sub(n, D(2))), D(2));
        Formula rhs = Mul(D(3), Pow(m, D(6)));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("n"), Bound("M"), Bound("t"), Bound("R1"),
                Bound("R2"), Bound("delta1"), Bound("delta2")],
            new Formula.Logic(assumptions, FormulaLogicOperator.Implies,
                Le(lhs, rhs))));
    }

    private static Formula.BoundVariable Bound(string name) =>
        new(FormulaIdentifier.Create(name), Seq(Mathbb, Grp(F.Id("N"))));
    private static Formula Call(string name, params Formula[] args) =>
        Seq(F.Id(name), Parenthesized(Seq(args[0], Comma, Sp, args[1])));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Divides(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Divides, b);
    private static Formula And(params Formula[] parts) => parts.Aggregate(
        (a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
}
