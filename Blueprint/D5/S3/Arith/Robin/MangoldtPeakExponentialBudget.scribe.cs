using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class MangoldtPeakExponentialBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The consumed final exponential budget.",
        H("The consumed final exponential budget"),
        Blocks(
                Paragraph(Text("For delta>0, D>0 and m>=100*D^2/delta^2, multiplying the lower-time inequality by m gives 100*m*D^2<=m^2*delta^2. Consequently 4000*m*D^2<(17*delta*m)^2/2. The existing Real.pow_div_factorial_le_exp at degree two supplies the strict final inequality 4000*m*D^2<exp(17*delta*m).")),
                Paragraph(Text("OriginalPositiveUPeak uses this bound in the final contradiction. The Taylor specialization is a consumed bind-only helper, not an independent novelty claim or a new application theorem.")))));
}
