using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Dilation;

internal sealed class GoldenUnitZetaPeriodicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden-unit lattice zeta is periodic along the regulator flow.",
        H("Golden Unit Zeta Periodicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-unit-zeta-periodicity"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Dilation/GoldenUnitZetaPeriodicity.golden_unit_zeta_periodicity"),
                H("The golden unit gives the regulator period"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A coefficient pair (a,b) represents the quadratic integer a+b phi. "
                        + "The statement exposes both real embeddings, the anisotropic form, "
                        + "and the zeta sum over the nonzero coefficient lattice.")),
                    Paragraph(Text(
                        "Multiplication by phi is the integral bijection (a,b) maps to "
                        + "(b,a+b). Its two embeddings scale by phi and its conjugate, so "
                        + "reindexing the totalized sum shifts the flow parameter by twice "
                        + "log(phi) without changing the value."))),
                DescribeRole.Theorem)),
        []));

    private static Formula TheoremFormula()
    {
        Formula integers = F.Seq(F.Mathbb, F.Grp(F.Id("Z")));
        Formula reals = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula complexes = F.Seq(F.Mathbb, F.Grp(F.Id("C")));
        Formula pair = F.Seq(integers, F.Sp, F.Times, F.Sp, integers);
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula alpha = F.Id("alpha");
        Formula eta = F.Id("eta");
        Formula s = F.Id("s");
        Formula pairValue = F.Seq(F.Open, a, F.Comma, F.Sp, b, F.Close);
        Formula sigmaPlusAtPair = Call("sigmaPlus", pairValue);
        Formula sigmaMinusAtPair = Call("sigmaMinus", pairValue);
        Formula nonzeroCarrier = F.Seq(
            F.Grp(pair), F.Sp, F.Setminus, F.Sp,
            F.OpenBrace, F.Open, F.D(0), F.Comma, F.Sp, F.D(0), F.Close,
            F.CloseBrace);
        Formula period = F.Seq(
            F.D(2), F.Sp, F.Cdot, F.Sp,
            Call("log", F.Varphi));
        Formula formDefinition = F.Seq(
            Call("exp", eta), F.Sp, F.Times, F.Sp,
            Pow(sigmaPlusAtPair, F.D(2)),
            F.Sp, F.Plus, F.Sp,
            Call("exp", F.Seq(F.Minus, eta)), F.Sp, F.Times, F.Sp,
            Pow(sigmaMinusAtPair, F.D(2)));
        Formula zetaDefinition = F.Seq(
            F.Sum, F.Underscore,
            F.Grp(alpha, F.Sp, F.InMacro, F.Sp, nonzeroCarrier), F.Sp,
            Pow(
                Call("anisotropicForm", eta, alpha),
                F.Seq(F.Minus, s)));

        return F.Disp(new Formula.Aligned([
            F.Seq(
                F.Id("sigmaPlus"), F.Colon, F.Sp, pair, F.Sp, F.To, F.Sp, reals,
                F.Comma, F.Sp, sigmaPlusAtPair, F.Sp, F.Colon, F.Eq, F.Sp,
                a, F.Sp, F.Plus, F.Sp, b, F.Sp, F.Times, F.Sp, F.Varphi,
                F.Comma),
            F.Seq(
                F.Id("sigmaMinus"), F.Colon, F.Sp, pair, F.Sp, F.To, F.Sp, reals,
                F.Comma, F.Sp, sigmaMinusAtPair, F.Sp, F.Colon, F.Eq, F.Sp,
                a, F.Sp, F.Plus, F.Sp, b, F.Sp, F.Times, F.Sp, F.Psi,
                F.Comma),
            F.Seq(
                F.Id("anisotropicForm"), F.Colon, F.Sp, reals, F.Sp, F.To, F.Sp,
                pair, F.Sp, F.To, F.Sp, reals, F.Comma, F.Sp,
                Call("anisotropicForm", eta, pairValue), F.Sp, F.Colon, F.Eq, F.Sp,
                formDefinition, F.Comma),
            F.Seq(
                F.Id("goldenUnitZeta"), F.Colon, F.Sp, complexes, F.Sp, F.To, F.Sp,
                reals, F.Sp, F.To, F.Sp, complexes, F.Comma, F.Sp,
                Call("goldenUnitZeta", s, eta), F.Sp, F.Colon, F.Eq, F.Sp,
                zetaDefinition, F.Comma),
            F.Seq(
                F.Forall, F.Sp, s, F.Sp, F.InMacro, F.Sp, complexes, F.Comma, F.Sp,
                F.Forall, F.Sp, eta, F.Sp, F.InMacro, F.Sp, reals, F.Comma, F.Sp,
                Call("goldenUnitZeta", s, F.Seq(eta, F.Sp, F.Plus, F.Sp, period)),
                F.Sp, F.Eq, F.Sp, Call("goldenUnitZeta", s, eta), F.Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { F.Operatorname, F.Grp(F.Id(name)), F.Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(F.Comma);
                pieces.Add(F.Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(F.Close);
        return F.Seq([.. pieces]);
    }

    private static Formula Pow(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));
}
