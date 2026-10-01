using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class Erdos699JointAdjacentCoresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two adjacent congruences force nontrivial factors at three consecutive integers.",
        H("Erdos 699 Joint Adjacent Cores"),
        Blocks(Describe.Lean(
            DescribeId.Create("erdos699-joint-adjacent-gcds"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Erdos699JointAdjacentCores.erdos699_joint_adjacent_gcds"),
            H("Three nontrivial adjacent gcds"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "B and s are integers. The hypotheses are B at least 5 and odd, "
                    + "1 <= s <= B-1, (2B+1) divides 4s squared minus 1, and B divides "
                    + "(s-1)s(s+1). Each of the three displayed gcds exceeds 1.")),
                Paragraph(Text(
                    "The quotient A=(4s squared minus 1)/(2B+1) satisfies 0<A<2B "
                    + "and A=1 modulo 4. Assuming any one gcd is 1 gives a contradiction "
                    + "after cancellation modulo B. The three nontrivial gcds are pairwise "
                    + "coprime, so B has at least three distinct prime factors. This is a "
                    + "necessary condition in one i=3 slice and does not resolve Erdős 699."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula b = F.Id("B"), s = F.Id("s");
        Formula sm = Sub(s, D(1)), sp = Add(s, D(1));
        Formula hypotheses = And(
            Le(D(5), b), new Formula.Apply(F.Id("Odd"), [b]),
            Le(D(1), s), Le(s, Sub(b, D(1))),
            Divides(Add(Mul(D(2), b), D(1)), Sub(Mul(D(4), Pow(s, D(2))), D(1))),
            Divides(b, Mul(Mul(sm, s), sp)));
        Formula conclusion = And(
            Lt(D(1), Gcd(b, sm)), Lt(D(1), Gcd(b, s)), Lt(D(1), Gcd(b, sp)));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("B"), Bound("s")],
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name) =>
        new(FormulaIdentifier.Create(name), Seq(Mathbb, Grp(F.Id("Z"))));
    private static Formula Gcd(Formula a, Formula b) =>
        new Formula.Apply(F.Id("gcd"), [a, b]);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Divides(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Divides, b);
    private static Formula And(params Formula[] parts) => parts.Aggregate(
        (a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
}
