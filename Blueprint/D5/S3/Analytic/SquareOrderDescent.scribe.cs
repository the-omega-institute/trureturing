using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class SquareOrderDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square-root rescaling of a radial maximum-modulus function halves its logarithmic order.",
        H("Square Order Descent"),
        Blocks(Describe.Lean(
            DescribeId.Create("square-root-maximum-modulus-order-descent"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/SquareOrderDescent.square_order_descent"),
            H("Square-root rescaling halves logarithmic order"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let M_F and M_G be real radial maximum-modulus functions. Assume M_F is "
                        + "eventually greater than one, so its nested logarithm uses the standard "
                        + "positive branch, and assume M_G(r) equals M_F(sqrt(r)) at every "
                        + "nonnegative radius. Then M_G is also eventually greater than one.")),
                Paragraph(Text(
                    "Define rho(M) as the extended-real upper limit of log(log(M(r))) divided "
                        + "by log(r) as r tends to infinity. The identity log(sqrt(r)) = log(r)/2 "
                        + "away from the degenerate radii gives rho(M_G) = rho(M_F)/2. In "
                        + "particular, order one descends to order one half.")),
                Paragraph(Text(
                    "The source statement did not specify a relationship between F and G; the "
                        + "displayed maximum-modulus rescaling is therefore an explicit hypothesis. "
                        + "The proof uses Mathlib's square-root filter map and nonnegative-constant "
                        + "limsup scaling theorem after restricting to radii greater than one."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula MF = new Formula.Subscript(F.Id("M"), F.Id("F"));
        Formula MG = new Formula.Subscript(F.Id("M"), F.Id("G"));
        Formula radius = F.Id("r");
        Formula rhoF = Apply(Rho, MF);
        Formula rhoG = Apply(Rho, MG);
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula orderDefinition = Seq(
            Apply(Rho, F.Id("M")), Sp, Colon, Eq, Sp,
            Operatorname, Grp(F.Id("limsup")), Underscore,
            Grp(radius, To, Sp, Infty), Sp,
            new Formula.Fraction(
                Grp(Log, Open, Log, Open,
                    Apply(F.Id("M"), radius), Close, Close),
                Grp(Log, Open, radius, Close)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, MF, Comma, Sp, MG, Colon, Sp,
            reals, Sp, To, Sp, reals, Comma, RowBreak, Grp(),
            Apply(F.Id("Eventually"), Seq(D(1), Sp, Lt, Sp,
                Apply(MF, radius))), Sp, Land, Sp,
            Open, Forall, Sp, radius, Sp, Geq, Sp, D(0), Comma, Sp,
            Apply(MG, radius), Sp, Eq, Sp,
            Apply(MF, Seq(Sqrt, Grp(radius))), Close,
            Sp, Rightarrow, RowBreak, Grp(),
            orderDefinition, Comma, Sp,
            Apply(F.Id("Eventually"), Seq(D(1), Sp, Lt, Sp,
                Apply(MG, radius))), Sp, Land, RowBreak, Grp(),
            rhoG, Sp, Eq, Sp, half, Sp, rhoF, Sp, Land, Sp,
            Open, rhoF, Sp, Eq, Sp, D(1), Sp, Rightarrow, Sp,
            rhoG, Sp, Eq, Sp, half, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);
}
