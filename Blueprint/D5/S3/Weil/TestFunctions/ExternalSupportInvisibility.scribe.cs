using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class ExternalSupportInvisibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula real = Call("Real"), complex = Call("Complex");
        Formula scale = F.Id("L"), source = F.Id("weilSource"), kappa = F.Id("kappa");
        Formula f = F.Id("f"), h = F.Id("h");
        Formula hfSmooth = F.Id("hfSmooth"), hhSmooth = F.Id("hhSmooth");
        Formula hfCompact = F.Id("hfCompact"), hhCompact = F.Id("hhCompact");
        Formula hfSupport = F.Id("hfSupport"), hhSupport = F.Id("hhSupport");
        Formula correlation = F.Id("correlation");
        Formula correlationCompact = F.Id("hcorrelationCompact");
        Formula correlationSmooth = F.Id("hcorrelationSmooth");
        Formula correlationTest = F.Id("correlationTest");
        Formula functionType = new Formula.TypeArrow(real, complex);
        Formula distributionType = Call("TemperedDistribution", real, complex);
        Formula doubledScale = new Formula.Binary(
            D(2), FormulaBinaryOperator.Multiply, scale);
        Formula innerInterval = Call("Ioo", new Formula.Negate(scale), scale);
        Formula outerInterval = Call(
            "Ioo", Seq(Minus, D(2), scale), doubledScale);
        Formula supportPremise = Seq(
            Call("dsupport", kappa), Sp, Subseteq, Sp, Call("compl", outerInterval));
        Formula correlationDefinition = Call("weilTest", f, h);
        Formula compactDefinition = Call(
            "weilTestHasCompactSupport", hfCompact, hhCompact);
        Formula smoothDefinition = Call(
            "contDiffConvolutionRight",
            Call("hasCompactSupportTilde", hhCompact),
            hfSmooth,
            Call("contDiffTilde", hhSmooth));
        Formula testDefinition = Call(
            "toSchwartzMap", correlation, correlationCompact, correlationSmooth);
        Formula conclusion = Equal(
            new Formula.Apply(Call("add", source, kappa), [correlationTest]),
            new Formula.Apply(source, [correlationTest]));

        Formula statement = Disp(new Formula.Aligned([
            Seq(Forall, Sp,
                scale, Colon, Sp, real, Comma, Sp,
                source, Comma, Sp, kappa, Colon, Sp, distributionType, Comma),
            Seq(F.Id("hkappa"), Colon, Sp, supportPremise, Comma, Sp,
                f, Comma, Sp, h, Colon, Sp, functionType, Comma),
            Seq(hfSmooth, Colon, Sp, Call("ContDiff", real, Call("infinity"), f), Comma, Sp,
                hhSmooth, Colon, Sp, Call("ContDiff", real, Call("infinity"), h), Comma),
            Seq(hfCompact, Colon, Sp, Call("HasCompactSupport", f), Comma, Sp,
                hhCompact, Colon, Sp, Call("HasCompactSupport", h), Comma),
            Seq(hfSupport, Colon, Sp, Call("tsupport", f), Sp, Subseteq, Sp, innerInterval,
                Comma, Sp, hhSupport, Colon, Sp, Call("tsupport", h), Sp, Subseteq, Sp,
                innerInterval, Sp, Rightarrow),
            Seq(Operatorname, Grp(F.Id("let")), Sp, correlation, Sp, Colon, Eq, Sp,
                correlationDefinition, Comma),
            Seq(Operatorname, Grp(F.Id("let")), Sp, correlationCompact, Colon, Sp,
                Call("HasCompactSupport", correlation), Sp, Colon, Eq, Sp,
                compactDefinition, Comma),
            Seq(Operatorname, Grp(F.Id("let")), Sp, correlationSmooth, Colon, Sp,
                Call("ContDiff", real, Call("infinity"), correlation), Sp, Colon, Eq, Sp,
                smoothDefinition, Comma),
            Seq(Operatorname, Grp(F.Id("let")), Sp, correlationTest, Sp, Colon, Eq, Sp,
                testDefinition, Comma),
            Seq(conclusion, Dot),
        ]));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A compactly supported Weil correlation is unchanged by adding a tempered "
                + "distribution whose distributional support lies outside its doubled window.",
            H("External-Support Invisibility"),
            Blocks(Describe.Lean(
                DescribeId.Create("external-support-invisibility"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/TestFunctions/ExternalSupportInvisibility."
                        + "external_support_invisibility"),
                H("External support is invisible to local Weil correlations"),
                StatementSource.FromAuthor(statement),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The canonical Weil correlation is constructed from the two supplied "
                        + "smooth compact tests. Its strict doubled-window support permits a "
                        + "finite smooth partition-of-unity decomposition into neighborhoods "
                        + "where the added tempered distribution vanishes."))),
                DescribeRole.Theorem))));
    }
}
