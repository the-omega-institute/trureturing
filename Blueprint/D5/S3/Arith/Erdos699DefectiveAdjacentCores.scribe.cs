using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class Erdos699DefectiveAdjacentCoresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two congruence conditions force nontrivial factors at three consecutive integers.",
        H("Erdos 699 Defective Adjacent Cores"),
        Blocks(Describe.Lean(
            DescribeId.Create("erdos699-defective-adjacent-gcds"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Erdos699DefectiveAdjacentCores.erdos699_defective_adjacent_gcds"),
            H("Three nontrivial adjacent gcds"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "b and s are integers. The hypotheses are b at least 5 and odd, "
                    + "b congruent to 5 modulo 8, b congruent to 8 modulo 19, "
                    + "1 <= s <= 3b-3, (6b+1) divides 4s squared minus 1, and b divides "
                    + "(s-1)s(s+1). Each of the three displayed gcds exceeds 1.")),
                Paragraph(Text(
                    "Writing (6b+1)A=4s squared minus 1 gives 0<A<6b and A congruent "
                    + "to 1 modulo 4. A unit gcd at s gives a square congruent to 5 "
                    + "modulo 8; a unit gcd at s+1 gives an impossible square bound; "
                    + "a unit gcd at s-1 gives a square congruent to 2 or 3 modulo 19. "
                    + "Thus all three adjacent gcds are nontrivial. This is a necessary "
                    + "condition in one Erdos 699 slice and does not resolve the full problem."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula b = F.Id("b"), s = F.Id("s");
        Formula sm = Sub(s, N(1)), sp = Add(s, N(1));
        Formula hypotheses = And(
            Le(N(5), b), new Formula.Apply(F.Id("Odd"), [b]),
            Congruent(b, N(5), N(8)), Congruent(b, N(8), D(1, 9)),
            Le(N(1), s), Le(s, Sub(Mul(N(3), b), N(3))),
            Divides(Add(Mul(N(6), b), N(1)), Sub(Mul(N(4), Pow(s, N(2))), N(1))),
            Divides(b, Mul(Mul(sm, s), sp)));
        Formula conclusion = And(
            Lt(N(1), Gcd(b, sm)), Lt(N(1), Gcd(b, s)), Lt(N(1), Gcd(b, sp)));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("b"), Bound("s")],
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name) =>
        new(FormulaIdentifier.Create(name), Seq(Mathbb, Grp(F.Id("Z"))));
    private static Formula N(byte digit) => new Formula.LatexDigits([digit]);
    private static Formula Congruent(Formula left, Formula right, Formula modulus) =>
        Seq(left, Sp, Equiv, Sp, right, Sp,
            Seq(Open, Mathrm, Grp(F.Id("mod")), Sp, modulus, Close));
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
