using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Feedback;

internal sealed class StrategicResponseObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed-point-free strategic response prevents any predictor from being correct at every state.",
        H("Strategic Response Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strategic-response-precludes-universal-predictor"),
                DeclarationHandle.Create(
                    "D5/S0/Diagonal/Feedback/StrategicResponseObstruction.strategic_response_precludes_universal_predictor"),
                H("Strategic response precludes a universal predictor"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open,
                    Forall, Sp, F.Id("y"), Comma, Esc,
                    F.Id("tau"), Open, F.Id("y"), Close, Sp, Neq, Sp, F.Id("y"),
                    Close, Sp, Land, Sp, Open,
                    Forall, Sp, F.Id("f"), Comma, Esc, Exists, Sp, F.Id("x"), Comma, Esc,
                    F.Id("R"), Open, F.Id("f"), Comma, F.Id("x"), Close, Sp, Eq, Sp,
                    F.Id("tau"), Open, F.Id("f"), Open, F.Id("x"), Close, Close,
                    Close, Sp, Rightarrow, Sp,
                    Neg, Sp, Exists, Sp, F.Id("f"), Comma, Esc, Forall, Sp, F.Id("x"), Comma, Esc,
                    F.Id("R"), Open, F.Id("f"), Comma, F.Id("x"), Close, Sp, Eq, Sp,
                    F.Id("f"), Open, F.Id("x"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a proposed predictor and choose the response state supplied by the "
                        + "strategic hypothesis. Universal correctness identifies the response with "
                        + "the prediction there, while strategic response identifies it with the "
                        + "twisted prediction. Their equality makes that prediction a fixed point of "
                        + "the twist, contradicting the fixed-point-free hypothesis.")),
                    Paragraph(Text(
                        "Pinned Mathlib, Loogle, and D5 were searched before proving. Mathlib's "
                        + "Function.IsFixedPt supplies the standard fixed-point predicate, but no "
                        + "library theorem has this predictor-dependent response hypothesis and "
                        + "universal-correctness conclusion."))),
                DescribeRole.Theorem))));
}
