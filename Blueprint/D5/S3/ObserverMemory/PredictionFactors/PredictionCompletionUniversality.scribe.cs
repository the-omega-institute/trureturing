using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionFactors;

internal sealed class PredictionCompletionUniversalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatible coarse dynamics determine the complete future readout.",
        H("Prediction Completion Universality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("compatible-coarse-dynamics-complete-the-future-trace"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionFactors/PredictionCompletionUniversality."
                        + "prediction_completion_universality"),
                H("Compatible coarse dynamics complete the future trace"),
                StatementSource.FromAuthor(UniversalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F update source states, let q read them out, and let r map source "
                            + "states to coarse states. Suppose r intertwines F with a coarse "
                            + "update G and q factors through a coarse readout h.")),
                    Paragraph(Text(
                        "Define the completed coarse readout at time n by applying h after the "
                            + "n-fold iterate of G. The iterate-semiconjugacy law then identifies "
                            + "this value with the source readout after the n-fold iterate of F.")),
                    Paragraph(Text(
                        "The Lean theorem uses the existing complete-itinerary primitive. Pinned "
                            + "Mathlib supplies Function.semiconj_iff_comp_eq and the exact "
                            + "iterate transport theorem Function.Semiconj.iterate_right; both "
                            + "are applied directly."))),
                DescribeRole.Theorem))));

    private static Formula Typed(string name, Formula type) =>
        Seq(F.Id(name), Colon, Sp, type);

    private static Formula UniversalityFormula()
    {
        Formula xType = F.Id("X");
        Formula outputType = F.Id("B");
        Formula coarseType = F.Id("C");
        Formula sourceStep = F.Id("F");
        Formula readout = F.Id("q");
        Formula coarseState = F.Id("r");
        Formula coarseStep = F.Id("G");
        Formula coarseReadout = F.Id("h");
        Formula completion = F.Id("Phi");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula futureTrace = Call("Tr", readout, sourceStep);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, xType, Comma, Sp, outputType, Comma, Sp, coarseType, Comma, RowBreak,
            Typed("F", new Formula.TypeArrow(xType, xType)), Comma, Sp,
            Typed("q", new Formula.TypeArrow(xType, outputType)), Comma, RowBreak,
            Typed("r", new Formula.TypeArrow(xType, coarseType)), Comma, Sp,
            Typed("G", new Formula.TypeArrow(coarseType, coarseType)), Comma, Sp,
            Typed("h", new Formula.TypeArrow(coarseType, outputType)), Comma, RowBreak,
            Open,
            coarseState, Sp, Circ, Sp, sourceStep, Sp, Eq, Sp,
            coarseStep, Sp, Circ, Sp, coarseState, Sp, Land, Sp,
            readout, Sp, Eq, Sp, coarseReadout, Sp, Circ, Sp, coarseState,
            Close, Sp, Rightarrow, RowBreak,
            Exists, Sp, completion, Colon, Sp,
            new Formula.TypeArrow(coarseType, new Formula.TypeArrow(naturals, outputType)),
            Comma, Sp, futureTrace, Sp, Eq, Sp,
            completion, Sp, Circ, Sp, coarseState, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
