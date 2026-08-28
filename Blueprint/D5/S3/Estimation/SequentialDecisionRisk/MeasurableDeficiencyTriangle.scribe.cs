using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.SequentialDecisionRisk;

internal sealed class MeasurableDeficiencyTriangleDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/SequentialDecisionRisk/MeasurableDeficiencyTriangle."
            + "measurable_deficiency_triangle";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One-way deficiency of arbitrary measurable statistical experiments satisfies the "
            + "triangle inequality under Markov simulator composition.",
        H("Measurable Deficiency Triangle"),
        Blocks(Describe.Lean(
            DescribeId.Create("measurable-deficiency-triangle"),
            DeclarationHandle.Create(Declaration),
            H("Measurable experiment deficiency obeys the triangle inequality"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The one-way deficiency is constructed as the infimum over Markov "
                        + "simulators of the supremum, over parameter states, of measurable-event "
                        + "total variation.")),
                Paragraph(Text(
                    "Two simulators compose. The measure-level triangle inequality separates "
                        + "their errors, while a layer-cake argument proves that applying the "
                        + "second Markov kernel contracts total variation. The pointwise estimate "
                        + "then passes through the supremum and the two independent infima."))),
            DescribeRole.Theorem))));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula state = F.Id("Theta");
        Formula firstObservation = F.Id("X");
        Formula middleObservation = F.Id("Y");
        Formula finalObservation = F.Id("Z");
        Formula first = F.Id("E");
        Formula middle = F.Id("F");
        Formula final = F.Id("G");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(state, Comma, Sp, firstObservation, Comma, Sp,
                middleObservation, Comma, Sp, finalObservation), type),
            Comma, RowBreak, Grp(),
            Call("MeasurableSpace", state), Comma, Sp,
            Call("MeasurableSpace", firstObservation), Comma, Sp,
            Call("MeasurableSpace", middleObservation), Comma, Sp,
            Call("MeasurableSpace", finalObservation), Comma, RowBreak, Grp(),
            Typed(first, Call("Kernel", state, firstObservation)), Comma, Sp,
            Call("IsMarkovKernel", first), Comma, RowBreak, Grp(),
            Typed(middle, Call("Kernel", state, middleObservation)), Comma, Sp,
            Call("IsMarkovKernel", middle), Comma, RowBreak, Grp(),
            Typed(final, Call("Kernel", state, finalObservation)), Comma, Sp,
            Call("IsMarkovKernel", final), Sp, Rightarrow, RowBreak, Grp(),
            Call("measurableDeficiency", final, first), Sp, Leq, Sp,
            Call("measurableDeficiency", final, middle), Sp, Plus, Sp,
            Call("measurableDeficiency", middle, first), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
