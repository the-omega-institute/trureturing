using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Dilation;

internal sealed class ActualRegularLedgerCollisionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Dilation/ActualRegularLedgerCollision.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A regular and a trivial graded rational representation have equal formal-log histories on one conjugacy class.",
        H("Regular Ledger Collision"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("regular-ledger-cyclic-determinant"),
                DeclarationHandle.Create(Owner + "single_cycle_det"),
                H("Determinant of a cyclic permutation"),
                StatementSource.FromAuthor(CycleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive cycle length r, the determinant of the identity "
                            + "minus X times the matrix of the cyclic rotation of Fin r is "
                            + "1-X^r over the rational polynomial ring. The proof replaces the "
                            + "final row by a weighted sum of all rows. The resulting matrix is "
                            + "upper triangular, with final diagonal entry 1-X^r; the same "
                            + "calculation includes a one-element cycle."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-regular-ledger-conjugacy-collision"),
                DeclarationHandle.Create(Owner + "actual_ledger_collision"),
                H("Collision of actual graded representations"),
                StatementSource.FromAuthor(CollisionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let G be a finite group and let g have order r greater than one. "
                            + "Write N for the cardinality of G and c=N/r, which is positive. "
                            + "The rational G-representation A has the left regular module "
                            + "Q[G] in bidegree (1,1) and the zero module in every other "
                            + "bidegree. B has c copies of the trivial rational representation "
                            + "in bidegree (r,r) and the zero module elsewhere. At every "
                            + "bidegree, the coefficients of H_A and H_B equal the characters "
                            + "of these ledger entries; the PUnit zero modules have trace zero.")),
                    Paragraph(Text(
                        "For every h conjugate to g, left multiplication on G has c cycles "
                            + "of length r. Reindexing by right cosets of the subgroup generated "
                            + "by h gives the determinant (1-X^r)^c on Q[G]. The trivial action "
                            + "on Q^c gives the same determinant when weighted by X^r. "
                            + "Substitution X=pq defines a bivariate denominator with constant "
                            + "coefficient one from either actual determinant.")),
                    Paragraph(Text(
                        "Its negative formal logarithm is the entire class-indexed "
                            + "logarithmic history of both trace series at h, including zero and "
                            + "off-diagonal coefficients. The raw coefficient in bidegree (r,r) "
                            + "is zero for A and c for B. The assertion concerns only conjugates "
                            + "of g; it gives no equality at every group element or every power "
                            + "and makes no claim about a Monster root space or a vertex algebra."))),
                DescribeRole.Theorem))));

    private static Formula CycleFormula()
    {
        Formula r = F.Id("r"), x = F.Id("X"), p = F.Id("P");
        Formula permutation = new Formula.Subscript(p, r);
        return F.Disp(new Formula.Aligned([
            F.Seq(F.Forall, F.Sp, r, F.Sp, F.InMacro, F.Sp, Naturals(),
                F.Comma, F.Sp, F.D(0), F.Sp, F.Lt, F.Sp, r, F.Sp, F.Rightarrow),
            Equal(Call("det", F.Seq(F.Id("I"), F.Sp, F.Minus, F.Sp,
                    x, F.Sp, permutation)),
                F.Seq(F.D(1), F.Sp, F.Minus, F.Sp, Pow(x, r))),
        ]));
    }

    private static Formula CollisionFormula()
    {
        Formula g = F.Id("g"), h = F.Id("h"), r = F.Id("r");
        Formula c = F.Id("c"), n = F.Id("N"), x = F.Id("X");
        Formula p = F.Id("p"), q = F.Id("q");
        Formula a = F.Id("A"), b = F.Id("B"), d = F.Id("D");
        Formula ha = new Formula.Subscript(F.Id("H"), a);
        Formula hb = new Formula.Subscript(F.Id("H"), b);
        Formula xPower = Pow(x, r);
        Formula factor = Pow(F.Grp(F.D(1), F.Sp, F.Minus, F.Sp, xPower), c);
        Formula grade(Formula ledger, Formula first, Formula second) =>
            new Formula.Subscript(ledger, F.Seq(first, F.Comma, second));
        Formula pair(Formula first, Formula second) => Call("pair", first, second);
        Formula history(Formula series) => Call("Phi", series, h);
        Formula coefficient(Formula series) => Call("coeff", series, r, r);

        return F.Disp(new Formula.Aligned([
            F.Seq(F.Id("G"), F.Sp, F.InMacro, F.Sp, Call("FiniteGroup"),
                F.Comma, F.Sp, g, F.Sp, F.InMacro, F.Sp, F.Id("G"), F.Comma),
            F.Seq(Equal(r, Call("ord", g)), F.Comma, F.Sp,
                F.D(1), F.Sp, F.Lt, F.Sp, r, F.Comma, F.Sp,
                Equal(n, Call("card", F.Id("G"))), F.Comma, F.Sp,
                Equal(c, new Formula.Fraction(n, r)), F.Comma, F.Sp,
                F.D(0), F.Sp, F.Lt, F.Sp, c),
            F.Seq(Equal(grade(a, F.D(1), F.D(1)), Call("regular", F.Id("G"))),
                F.Comma, F.Sp, Equal(grade(b, r, r), Call("trivial", c))),
            F.Seq(Call("support", a), F.Sp, F.Eq, F.Sp,
                Call("singleton", pair(F.D(1), F.D(1))), F.Comma, F.Sp,
                Call("support", b), F.Sp, F.Eq, F.Sp,
                Call("singleton", pair(r, r))),
            F.Seq(Equal(ha, Call("traceSeries", a)), F.Comma, F.Sp,
                Equal(hb, Call("traceSeries", b))),
            F.Seq(F.Exists, F.Sp, d, F.Comma, F.Sp),
            F.Seq(F.Forall, F.Sp, h, F.Sp, F.InMacro, F.Sp, Call("Conj", g),
                F.Comma, F.Sp),
            F.Seq(Equal(Call("detRegular", h, x), factor), F.Comma, F.Sp,
                Equal(Call("detTrivial", h, xPower), factor)),
            F.Seq(Equal(d, Call("substitute", factor, F.Seq(p, q))),
                F.Comma, F.Sp,
                Equal(Call("negativeLog", d), history(ha)), F.Comma, F.Sp,
                Equal(Call("negativeLog", d), history(hb))),
            F.Seq(Equal(history(ha), history(hb)), F.Comma, F.Sp,
                Equal(coefficient(ha), F.D(0)), F.Sp, F.Neq, F.Sp, c, F.Sp,
                F.Eq, F.Sp, coefficient(hb)),
        ]));
    }

    private static Formula Naturals() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Pow(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));
}
