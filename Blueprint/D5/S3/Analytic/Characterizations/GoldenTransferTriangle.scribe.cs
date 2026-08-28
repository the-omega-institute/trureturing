using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Characterizations;

internal sealed class GoldenTransferTriangleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp disk radius, inverse fixed point, local derivative, and shortest-orbit scale "
        + "are all governed by the golden ratio.",
        H("Golden Transfer Triangle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-transfer-triangle"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Characterizations/GoldenTransferTriangle."
                        + "golden_transfer_triangle"),
                H("The golden transfer quantities agree"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source disk inequality is equivalent, on radii at least one, to "
                            + "the open interval ending at phi. Its least upper bound is therefore "
                            + "the golden ratio.")),
                    Paragraph(Text(
                        "The quadratic identity for phi gives the reciprocal fixed point. Direct "
                            + "differentiation of x mapped to one over x plus one gives the inverse-"
                            + "square derivative magnitude, and four exponential-log factors give "
                            + "the inverse fourth power."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula r = F.Id("r");
        Formula one = D(1);
        Formula two = D(2);
        Formula radiusPredicate = new Formula.Logic(
            new Formula.Relation(one, FormulaRelationOperator.LessThanOrEqual, r),
            FormulaLogicOperator.And,
            new Formula.Logic(
                new Formula.Relation(r, FormulaRelationOperator.LessThan, two),
                FormulaLogicOperator.And,
                new Formula.Relation(
                    new Formula.Fraction(one, Subtract(two, r)),
                    FormulaRelationOperator.LessThan,
                    Add(one, r))));
        Formula radiusSet = Seq(
            Left, OpenBrace, r, Sp, InMacro, Sp, Reals(), Sp, Mid, Sp,
            radiusPredicate, Right, CloseBrace);
        Formula sharpRadius = Call("IsLUB", radiusSet, Varphi);
        Formula fixedPoint = Equal(
            Subtract(Varphi, one),
            new Formula.Power(Varphi, Seq(Minus, one)));
        Formula branch = Seq(
            F.Id("x"), Sp, Mapsto, Sp,
            new Formula.Fraction(one, Add(F.Id("x"), one)));
        Formula derivative = Equal(
            new Formula.Absolute(Call("deriv", branch, Subtract(Varphi, one))),
            new Formula.Power(Varphi, Seq(Minus, D(2))));
        Formula orbit = Equal(
            Call("exp", Seq(Minus, Open, D(4), Sp, Call("log", Varphi), Close)),
            new Formula.Power(Varphi, Seq(Minus, D(4))));
        return Disp(new Formula.Logic(
            sharpRadius,
            FormulaLogicOperator.And,
            new Formula.Logic(
                fixedPoint,
                FormulaLogicOperator.And,
                new Formula.Logic(derivative, FormulaLogicOperator.And, orbit))));
    }

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }
            pieces.Add(arguments[index]);
        }
        pieces.Add(Close);
        return Seq(pieces.ToArray());
    }
}
