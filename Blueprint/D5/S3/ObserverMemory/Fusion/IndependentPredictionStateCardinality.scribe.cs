using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Fusion;

internal sealed class IndependentPredictionStateCardinalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent predictive components have a product completion and multiplicative finite state count.",
        H("Independent Prediction State Cardinality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-independent-prediction-state-cardinality"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Fusion/IndependentPredictionStateCardinality."
                        + "finite_independent_prediction_state_cardinality"),
                H("Independent prediction state cardinality is multiplicative"),
                StatementSource.FromAuthor(CardinalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The predictive state count is the finite cardinality of a completed-state "
                            + "carrier. Assume that the completed states of both component systems "
                            + "are finite.")),
                    Paragraph(Text(
                        "For the componentwise product update and paired product readout, the global "
                            + "completed-state quotient is equivalent to the Cartesian product of the "
                            + "two component quotients. Consequently its predictive state count is the "
                            + "product, rather than the sum, of the two component counts.")),
                    Paragraph(Text(
                        "The previously established independent-product equivalence supplies the "
                            + "decomposition. Invariance of finite cardinality under equivalence and "
                            + "the cardinality rule for product types then give the multiplication law. "
                            + "The result concerns two components and does not assert a general "
                            + "finite-family decomposition."))),
                DescribeRole.Theorem))));

    private static Formula CardinalityFormula()
    {
        Formula tau1 = F.Id("tau1");
        Formula tau2 = F.Id("tau2");
        Formula q1 = F.Id("q1");
        Formula q2 = F.Id("q2");
        Formula firstState = Call("CompletedState", tau1, q1);
        Formula secondState = Call("CompletedState", tau2, q2);
        Formula productState = Call(
            "CompletedState",
            Call("productUpdate", tau1, tau2),
            Call("productReadout", q1, q2));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, tau1, Comma, Sp, tau2, Comma, Sp,
            q1, Comma, Sp, q2, Comma, RowBreak, Grp(),
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp,
            firstState, CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp,
            secondState, CloseBracket, Comma, RowBreak,
            Operatorname, Grp(F.Id("Nonempty")), Open,
            productState, Sp, Equiv, Sp,
            Open, firstState, Close, Times, Open, secondState, Close, Close,
            Sp, Land, RowBreak,
            Call("predictiveStateCount", productState), Sp, Eq, Sp,
            Call("predictiveStateCount", firstState), Sp, Times, Sp,
            Call("predictiveStateCount", secondState), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
