using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValue;

internal sealed class OptimalBinaryAbstentionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary posterior loss selects answer zero, abstention, or answer one at the stated "
            + "thresholds.",
        H("Optimal Binary Answer with Abstention"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("optimal-binary-answer-with-abstention"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DecisionValue/OptimalBinaryAbstention."
                        + "optimal_binary_answer_with_abstention"),
                H("Optimal choice"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, F.Id("p"), Comma, Sp, LambdaLower, Colon, Sp,
                    Seq(Mathbb, Grp(F.Id("R"))), Comma, RowBreak, Grp(),
                    F.Id("hP"), Colon, Sp, F.Id("p"), InMacro, Sp,
                    OpenBracket, D(0), Comma, Sp, D(1), CloseBracket, Comma, Sp,
                    F.Id("hLambda"), Colon, Sp, LambdaLower, InMacro, Sp,
                    Open, D(0), Comma, Sp, Frac, Grp(D(1)), Grp(D(2)), Close,
                    Comma, RowBreak, Grp(),
                    new Formula.Apply(
                        Seq(Operatorname, Grp(F.Id("preferredBinaryAction"))),
                        [F.Id("p"), LambdaLower]),
                    Sp, Eq, Sp, Begin, Grp(F.Id("cases")),
                    F.Text, Grp(F.Id("answer"), Esc, D(0)), Comma, Amp,
                    F.Id("p"), Sp, Leq, Sp, LambdaLower, RowBreak, Grp(),
                    F.Text, Grp(F.Id("abstain")), Comma, Amp,
                    LambdaLower, Sp, Lt, Sp, F.Id("p"), Sp, Lt, Sp, D(1), Sp, Minus, Sp,
                    LambdaLower, RowBreak, Grp(),
                    F.Text, Grp(F.Id("answer"), Esc, D(1)), Comma, Amp,
                    F.Id("p"), Sp, Geq, Sp, D(1), Sp, Minus, Sp, LambdaLower,
                    End, Grp(F.Id("cases")), Dot, End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The binary target has posterior probability p of value one. Answering "
                            + "zero has expected loss p, abstaining has loss lambda, and answering "
                            + "one has expected loss 1-p.")),
                    Paragraph(Text(
                        "The selector is constructed by comparing those three losses, with the "
                            + "source's endpoint preference. Linear comparison yields answer zero "
                            + "below the lower threshold, abstention strictly between the "
                            + "thresholds, "
                            + "and answer one at and above the upper threshold."))),
                DescribeRole.Theorem))));
}
