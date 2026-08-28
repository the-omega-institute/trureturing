using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Characterizations;

internal sealed class ConnectionCoefficientCompositionDocument
    : IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S3/Constants/Characterizations/ConnectionCoefficientComposition."
            + "connection_coefficient_composition";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Connection coefficients compose multiplicatively along a two-step path.",
        H("Connection Coefficient Composition"),
        Blocks(Describe.Lean(
            DescribeId.Create("connection-coefficient-composition"),
            DeclarationHandle.Create(Gid),
            H("Connection coefficients multiply along composition"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The first clause quantifies the scalar and module carriers and states both "
                        + "successive path equations before deriving the product coefficient. "
                        + "Commutativity presents the coefficient in source order.")),
                Paragraph(Text(
                    "The second clause exposes the displayed positive-real certificate. The "
                        + "strictly positive x premise is the domain on which the reciprocal "
                        + "square-root scale is defined and the three factors multiply exactly."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("R");
        Formula carrier = F.Id("M");
        Formula type = F.Id("Type");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula xUpper = F.Id("X");
        Formula yUpper = F.Id("Y");
        Formula zUpper = F.Id("Z");
        Formula x = F.Id("x");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));

        Formula scale(Formula coefficient, Formula value) =>
            Seq(coefficient, Sp, Cdot, Sp, value);
        Formula coefficientLaw = Seq(
            Forall, Sp, scalar, Comma, Sp, carrier, Colon, Sp, type, Comma, Sp,
            Open,
                Call("CommSemiring", scalar), Sp, Land, Sp,
                Call("AddCommMonoid", carrier), Sp, Land, Sp,
                Call("Module", scalar, carrier),
            Close, Sp, Rightarrow, Sp,
            Forall, Sp, a, Comma, Sp, b, Colon, Sp, scalar, Comma, Sp,
            xUpper, Comma, Sp, yUpper, Comma, Sp, zUpper, Colon, Sp, carrier, Comma, Sp,
            Open,
                yUpper, Sp, Eq, Sp, scale(a, xUpper), Sp, Land, Sp,
                zUpper, Sp, Eq, Sp, scale(b, yUpper),
            Close, Sp, Rightarrow, Sp,
            zUpper, Sp, Eq, Sp, scale(Grp(a, Sp, Times, Sp, b), xUpper));

        Formula gaussian = Seq(Sqrt, Grp(Frac, Grp(Pi), Grp(D(2))));
        Formula exponential = Call("exp", Seq(Frac, Grp(x), Grp(D(2))));
        Formula scaleJacobian = Seq(
            x, Caret, Grp(Minus, Frac, Grp(D(1)), Grp(D(2))));
        Formula ramanujanLaw = Seq(
            Forall, Sp, x, Sp, InMacro, Sp, reals, Comma, Sp,
            D(0), Sp, Lt, Sp, x, Sp, Rightarrow, Sp,
            Sqrt, Grp(Frac,
                Grp(Pi, Sp, Times, Sp, Call("exp", x)),
                Grp(D(2), Sp, Times, Sp, x)),
            Sp, Eq, Sp,
            gaussian, Sp, Times, Sp, exponential, Sp, Times, Sp, scaleJacobian);

        return Disp(Seq(
            Open, coefficientLaw, Close, Sp, Land,
            RowBreak, Grp(),
            Open, ramanujanLaw, Close, Dot));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}
