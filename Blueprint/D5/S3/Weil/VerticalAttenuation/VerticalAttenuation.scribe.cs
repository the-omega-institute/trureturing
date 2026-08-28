using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.VerticalAttenuation;

internal sealed class VerticalAttenuationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite logarithmic modulus profile is the sum of its one-factor vertical attenuations.",
        H("Vertical Attenuation Tomography"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("vertical-attenuation-tomography"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/VerticalAttenuation/VerticalAttenuation."
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
        var app = (Formula f, Formula a) => Seq(f, Open, a, Close);
        var finite = Call("Fintype", F.Id("IndexType"));
        var profileLaw = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("x"), reals),
             new Formula.BoundVariable(FormulaIdentifier.Create("y"), reals)],
            Equal(app(app(profile, x), y), Call("finiteFactorSum", factor, x, y)));
        var positivity = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, y);
        var conclusion = Equal(app(A, y),
            Seq(Sum, Underscore, Grp(index, InMacro, finite), Sp,
                Call("min", y, app(realPart, index))));
        return Seq(
            Forall, Sp, F.Id("IndexType"), Colon, Sp, F.Id("Type"), Comma, Sp,
            finite, Sp, Rightarrow, Sp,
            Forall, Sp, A, Comma, Sp, Forall, Sp, profile, Comma, Sp,
            Forall, Sp, factor, Comma, Sp, Forall, Sp, realPart, Comma, Sp,
            profileLaw, Sp, Rightarrow, Sp,
            positivity, Sp, Rightarrow, Sp, conclusion);
    }
}
