using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class CompletionStateCardinalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A surjective refinement map makes completed-state cardinality monotone.",
        H("Completion State Cardinality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("completion-state-cardinality-is-monotone-under-refinement"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Prediction/CompletionStateCardinality."
                        + "completion_state_cardinality_mono"),
                H("Completion state cardinality is monotone under refinement"),
                StatementSource.FromAuthor(CardinalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Fine and Coarse be finite completed-state carriers. If a forgetting "
                            + "map sends Fine surjectively onto Coarse, then the number of coarse "
                            + "states is at most the number of refined states.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle returned the exact declaration "
                            + "Fintype.card_le_of_surjective, which is imported and applied "
                            + "directly. Repository searches found uses inside entropy and "
                            + "fusion bounds but no standalone completed-state refinement "
                            + "declaration. LeanSearch returned HTTP 405 and 422 and supplied no "
                            + "additional result.")),
                    Paragraph(Text(
                        "The theorem records only the finite cardinal consequence of the "
                            + "surjective refinement map. It assumes no entropy, probability, "
                            + "metric, dynamics, or strict decrease."))),
                DescribeRole.Theorem))));

    private static Formula Card(Formula type) =>
        Seq(Operatorname, Grp(F.Id("card")), Open, type, Close);

    private static Formula CardinalityFormula()
    {
        Formula fine = F.Id("Fine");
        Formula coarse = F.Id("Coarse");
        Formula forget = F.Id("forget");
        return Disp(Seq(
            Forall, Sp, fine, Comma, Sp, coarse, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, fine, CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, coarse, CloseBracket,
            Comma, Esc,
            forget, Colon, Sp, fine, Sp, To, Sp, coarse, Comma, Esc,
            Call("Surjective", forget), Sp, Rightarrow, Sp,
            Card(coarse), Sp, Leq, Sp, Card(fine), Dot));
    }
}
