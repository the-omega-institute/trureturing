using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Scattering;

internal sealed class VerticalAttenuationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite logarithmic modulus profile is the sum of its one-factor vertical attenuations.",
        H("Vertical Attenuation Tomography"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("vertical-attenuation-tomography"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Scattering/VerticalAttenuation."
                        + "vertical_attenuation_tomography"),
                H("Vertical attenuation is additive over the finite zero family"),
                StatementSource.FromAuthor(Disp(Formula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The real-line profile, its one-factor decomposition, and the finite "
                            + "factor integrability are public source laws. The one-factor "
                            + "Bode identity gives min(y, realPart i) after the 1/(4 pi) "
                            + "normalization.")),
                    Paragraph(Text(
                        "Finite-sum linearity of the Bochner integral then yields the exact "
                            + "modulus-only tomography formula for every positive height y."))),
                DescribeRole.Theorem))));

    private static Formula Formula()
    {
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var index = F.Id("i");
        var x = F.Id("x");
        var y = F.Id("y");
        var A = F.Id("A");
        var profile = F.Id("profile");
        var factor = F.Id("factor");
        var realPart = F.Id("realPart");
        var hA = F.Id("hA");
        var hdecomp = F.Id("hdecomp");
        var hintegrable = F.Id("hintegrable");
        var hone = F.Id("hone");
        var indexType = F.Id("IndexType");
        var app = (Formula f, Formula a) => Seq(f, Open, a, Close);
        var realFn = new Formula.TypeArrow(reals, reals);
        var profileFn = new Formula.TypeArrow(reals, realFn);
        var factorFn = new Formula.TypeArrow(indexType, profileFn);
        var realPartFn = new Formula.TypeArrow(indexType, reals);
        var finite = Call("Fintype", indexType);
        var oneOverFourPi = Seq(Frac, Grp(D(1)), Grp(Seq(D(4), Sp, Pi)));
        var integral = (Formula integrand, Formula variable) =>
            Seq(Int, Underscore, Grp(Mathbb, Grp(F.Id("R"))), Sp,
                integrand, Sp, F.Id("d"), variable);
        var lambda = (Formula variable, Formula body) =>
            Seq(Open, variable, Colon, Sp, reals, Sp, Mapsto, Sp, body, Close);
        var quantify = (Formula variable, Formula domain, Formula body) =>
            Seq(Forall, Sp, variable, Colon, Sp, domain, Comma, Sp, body);
        var factorAt = (Formula i, Formula coordinate, Formula height) =>
            app(app(app(factor, i), coordinate), height);
        var profileAt = (Formula coordinate, Formula height) => app(app(profile, coordinate), height);
        var sumAt = (Formula body) =>
            Seq(Sum, Underscore, Grp(Seq(index, Colon, Sp, indexType)), Sp, body);
        var normalizedIntegral = (Formula integrand, Formula variable) =>
            Seq(oneOverFourPi, Sp, Times, Sp, integral(integrand, variable));

        var hAType = quantify(y, reals,
            Equal(app(A, y), normalizedIntegral(profileAt(x, y), x)));
        var hdecompType = quantify(x, reals,
            quantify(y, reals,
                Equal(profileAt(x, y), sumAt(factorAt(index, x, y)))));
        var hintegrableType = quantify(index, indexType,
            quantify(y, reals,
                Call("Integrable", lambda(x, factorAt(index, x, y)))));
        var honeType = quantify(index, indexType,
            quantify(y, reals,
                new Formula.Logic(
                    new Formula.Relation(D(0), FormulaRelationOperator.LessThan, y),
                    FormulaLogicOperator.Implies,
                    Equal(normalizedIntegral(factorAt(index, x, y), x),
                        Call("min", y, app(realPart, index))))));
        var positivity = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, y);
        var conclusion = Equal(app(A, y),
            sumAt(Call("min", y, app(realPart, index))));

        return Seq(
            Forall, Sp, indexType, Colon, Sp,
            Seq(Operatorname, Grp(F.Id("Type"))), Comma, Sp,
            finite, Sp, Rightarrow, Sp,
            Forall, Sp, A, Colon, Sp, realFn, Comma, Sp,
            Forall, Sp, profile, Colon, Sp, profileFn, Comma, Sp,
            Forall, Sp, factor, Colon, Sp, factorFn, Comma, Sp,
            Forall, Sp, realPart, Colon, Sp, realPartFn, Comma, Sp,
            Forall, Sp, hA, Colon, Sp, hAType, Comma, Sp,
            Forall, Sp, hdecomp, Colon, Sp, hdecompType, Comma, Sp,
            Forall, Sp, hintegrable, Colon, Sp, hintegrableType, Comma, Sp,
            Forall, Sp, hone, Colon, Sp, honeType, Comma, Sp,
            quantify(y, reals, new Formula.Logic(positivity, FormulaLogicOperator.Implies, conclusion)));
    }
}
