using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class Erdos699DenominatorGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integral adjacent-column ratio forces a strict denominator gap in the Erdős 699 continuation.",
        H("Erdős 699 Denominator Gap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("erdos699-denominator-gap"),
                DeclarationHandle.Create("D5/S3/Arith/Erdos699DenominatorGap.erdos699_denominator_gap"),
                H("Strict gap from an integral ratio"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "All seven variables are integers. The hypotheses are exactly n >= 8, "
                            + "R > 0, m > 0, 2m < L, D > 0, n-1 = LR, j = 1+mR, and "
                            + "D(n-j)(n-j-1) = k(n-1)(n-2). No sign assumption is made on k. "
                            + "The conclusion is the strict bound 4(n-2) < DL squared.")),
                    Paragraph(Text(
                        "Eliminating n and j gives "
                            + "(D(L-m)^2-kL^2)(n-2) = D(L-m)m. The coefficient is a positive "
                            + "integer, so n-2 <= D(L-m)m. The strict inequality "
                            + "4(L-m)m < L^2 follows from L-2m > 0. This is a symbolic "
                            + "necessary condition. It does not prove any complete p=23,31,89 "
                            + "column or resolve Erdős 699."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n"), l = F.Id("L"), r = F.Id("R"), j = F.Id("j");
        Formula m = F.Id("m"), d = F.Id("D"), k = F.Id("k");
        Formula nMinusOne = Sub(n, D(1));
        Formula nMinusTwo = Sub(n, D(2));
        Formula nMinusJ = Sub(n, j);
        Formula hypotheses = And(
            Le(D(8), n), Lt(D(0), r), Lt(D(0), m), Lt(Mul(D(2), m), l),
            Lt(D(0), d), Eq(nMinusOne, Mul(l, r)),
            Eq(j, Add(D(1), Mul(m, r))),
            Eq(Mul(Mul(d, nMinusJ), Sub(nMinusJ, D(1))),
                Mul(Mul(k, nMinusOne), nMinusTwo)));
        Formula conclusion = Lt(Mul(D(4), nMinusTwo), Mul(d, Pow(l, D(2))));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("n"), Bound("L"), Bound("R"), Bound("j"), Bound("m"),
                Bound("D"), Bound("k")],
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name) =>
        new(FormulaIdentifier.Create(name), Seq(Mathbb, Grp(F.Id("Z"))));

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
    private static Formula And(params Formula[] parts) => parts.Aggregate(
        (a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
}
