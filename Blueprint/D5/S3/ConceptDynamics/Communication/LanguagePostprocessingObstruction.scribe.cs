using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Communication;

internal sealed class LanguagePostprocessingObstructionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Processing a language readout cannot recover a distinction absent from that readout.",
        H("Language Postprocessing Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("language-postprocessing-preserves-missing-distinction"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Communication/LanguagePostprocessingObstruction."
                        + "language_postprocessing_preserves_missing_distinction"),
                H("Language postprocessing preserves a missing distinction"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The language and phenomenon concepts are readouts on the same source "
                            + "carrier. Two public witness states share a language value while "
                            + "having different phenomenon values.")),
                    Paragraph(Text(
                        "For every output carrier and every function of the language value, "
                            + "equality transport makes the postprocessed outputs equal on the "
                            + "same witnesses.")),
                    Paragraph(Text(
                        "Thus longer text, richer rhetoric, or recursive interpretation cannot "
                            + "recover the missing distinction when its entire input still factors "
                            + "through the old language readout."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula languageType = new Formula.Subscript(F.Id("B"), F.Id("L"));
        Formula phenomenonType = new Formula.Subscript(F.Id("B"), F.Id("Phi"));
        Formula outputType = F.Id("Z");
        Formula language = F.Id("L");
        Formula phenomenon = F.Id("Phi");
        Formula postprocess = F.Id("h");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula languageX = Apply(language, x);
        Formula languageY = Apply(language, y);
        Formula phenomenonX = Apply(phenomenon, x);
        Formula phenomenonY = Apply(phenomenon, y);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, languageType, Comma, Sp,
            phenomenonType, Comma, Sp, outputType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            language, Colon, Sp, stateType, Sp, To, Sp, languageType, Comma, Sp,
            phenomenon, Colon, Sp, stateType, Sp, To, Sp, phenomenonType, Comma,
            RowBreak, Grp(),
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, stateType, Comma, RowBreak, Grp(),
            Open, languageX, Sp, Eq, Sp, languageY, Sp, Land, Sp,
            phenomenonX, Sp, Neq, Sp, phenomenonY, Close, Sp,
            Rightarrow, Sp, RowBreak, Grp(),
            Forall, Sp, postprocess, Colon, Sp, languageType, Sp, To, Sp,
            outputType, Comma, Sp,
            Apply(postprocess, languageX), Sp, Eq, Sp,
            Apply(postprocess, languageY), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
