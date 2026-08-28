using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Dilation;

internal sealed class GoldenUnitZetaReflectionDocument : IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S3/Analytic/Dilation/GoldenUnitZetaReflection."
            + "golden_unit_zeta_reflection";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjugation reflects the golden-unit flow, while unit multiplication supplies its period.",
        H("Golden Unit Zeta Reflection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-unit-zeta-reflection"),
                DeclarationHandle.Create(Gid),
                H("Conjugation and unit translation generate the flow symmetries"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A coefficient pair (a,b) represents the quadratic integer a+b phi. "
                            + "Both real embeddings, the anisotropic form, and the zeta sum over "
                            + "the nonzero coefficient lattice are exposed in the statement.")),
                    Paragraph(Text(
                        "Quadratic conjugation is the integral involution (a,b) maps to "
                            + "(a+b,-b). It exchanges the two real embeddings and therefore "
                            + "reindexes the zeta at eta as the zeta at minus eta. The second "
                            + "public conjunct imports the regulator-period theorem on exactly "
                            + "the same carrier, exposing both symmetry generators.")),
                    Paragraph(Text(
                        "Current D5 and pinned-Mathlib searches found no exact reflection theorem. "
                            + "The proof applies the canonical subtype equivalence and total-sum "
                            + "reindexing machinery; it does not define the zeta by its target "
                            + "symmetry or replace the coefficient lattice with a surrogate."))),
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
        Formula reflectionLaw = F.Seq(
            F.Forall, F.Sp, s, F.Sp, F.InMacro, F.Sp, complexes, F.Comma, F.Sp,
            F.Forall, F.Sp, eta, F.Sp, F.InMacro, F.Sp, reals, F.Comma, F.Sp,
            Call("goldenUnitZeta", s, eta), F.Sp, F.Eq, F.Sp,
            Call("goldenUnitZeta", s, F.Seq(F.Minus, eta)));
        Formula periodLaw = F.Seq(
            F.Forall, F.Sp, s, F.Sp, F.InMacro, F.Sp, complexes, F.Comma, F.Sp,
            F.Forall, F.Sp, eta, F.Sp, F.InMacro, F.Sp, reals, F.Comma, F.Sp,
            Call("goldenUnitZeta", s, F.Seq(eta, F.Sp, F.Plus, F.Sp, period)),
            F.Sp, F.Eq, F.Sp, Call("goldenUnitZeta", s, eta));

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
                F.Open, reflectionLaw, F.Close, F.Sp, F.Land, F.Sp,
                F.Open, periodLaw, F.Close, F.Dot),
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
