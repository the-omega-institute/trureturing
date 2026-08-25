using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class FiniteInterventionExtractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A separating intervention family on a finite model class has a finite separating subfamily.",
        H("Finite Intervention Extraction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-intervention-extraction"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Experiment/FiniteInterventionExtraction."
                        + "finite_intervention_extraction"),
                H("Finitely many interventions retain all target distinctions"),
                StatementSource.FromAuthor(ExtractionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The relevant universe consists of unordered pairs of finite models "
                            + "whose target values differ. The assumed intervention family "
                            + "covers this finite universe by its separation sets.")),
                    Paragraph(Text(
                        "A finite subcover therefore selects finitely many allowed "
                            + "interventions. Every target-distinct model pair is still "
                            + "separated by at least one selected intervention."))),
                DescribeRole.Theorem))));

    private static Formula ExtractionFormula()
    {
        Formula size = F.Id("n");
        Formula model = Call("Fin", size);
        Formula interventionType = F.Id("Intervention");
        Formula responseType = F.Id("Response");
        Formula targetType = F.Id("Target");
        Formula readout = F.Id("readout");
        Formula target = F.Id("target");
        Formula first = F.Id("i");
        Formula second = F.Id("j");
        Formula intervention = F.Id("a");
        Formula selected = F.Id("J");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula separation = Seq(
            Call("readout", intervention, first), Sp, Neq, Sp,
            Call("readout", intervention, second));

        return Disp(Seq(
            Forall, Sp, size, Sp, InMacro, Sp, NaturalNumbers(), Comma, Esc,
            interventionType, Comma, Sp, responseType, Comma, Sp, targetType,
            Colon, Sp, type, Comma, Esc,
            readout, Colon, Sp, interventionType, Sp, To, Sp,
            Open, model, Sp, To, Sp, responseType, Close, Comma, Esc,
            target, Colon, Sp, model, Sp, To, Sp, targetType, Comma, Esc,
            Open, Forall, Sp, first, Comma, Sp, second, Colon, Sp, model, Comma, Sp,
            Call("target", first), Sp, Neq, Sp, Call("target", second), Sp,
            Rightarrow, Sp, Exists, Sp, intervention, Colon, Sp, interventionType,
            Comma, Sp, separation, Close, Sp, Rightarrow, Sp,
            Exists, Sp, selected, Colon, Sp, Call("Set", interventionType), Comma, Esc,
            Call("Finite", selected), Sp, Land, Sp,
            Forall, Sp, first, Comma, Sp, second, Colon, Sp, model, Comma, Sp,
            Call("target", first), Sp, Neq, Sp, Call("target", second), Sp,
            Rightarrow, Sp, Exists, Sp, intervention, Colon, Sp, interventionType,
            Comma, Sp, intervention, Sp, InMacro, Sp, selected, Sp, Land, Sp,
            separation, Dot));
    }

    private static Formula NaturalNumbers() =>
        Seq(Mathbb, Grp(F.Id("N")));
}
