using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class FIBCycleRelaxationDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S1/Words/AdmissibleWords/FIBCycleRelaxation.cycle_completion_iff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cycle inequalities give the exact rectangular range of two FIB differences.",
        H("Cycle inequalities for two sources"),
        Blocks(
            Describe.Lean(DescribeId.Create("cycle-relaxation-gap"), DeclarationHandle.Create(Result),
                H("The exact range under cycle inequalities"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take nonnegative q and c with q plus c at most one. The distances from a "
                    + "fixed zero reference encode marginals q at S, T and W and q plus c at H and K. "
                    + "The proposed distances on SH, SK, WH, WK and TK are c. The queried "
                    + "distances on WS and TH are twice a and c plus twice b, corresponding to "
                    + "the oriented differences W outside S and T outside H. A symmetric completion "
                    + "satisfies all odd-subset cycle inequalities exactly when a lies between zero "
                    + "and the minimum of q and c, and b lies between zero and the minimum of q, "
                    + "c and the remaining mass outside H.")),
                    Paragraph(Text(
                    "Seven marked walks force the individual bounds. For sufficiency, the "
                    + "completion takes distance twice b on HK and the maximum of a and twice b "
                    + "on ST and WT. The resulting distances satisfy the triangle inequalities "
                    + "and each triangle has perimeter at most two. Both facts give the triangle "
                    + "law on two copies of the vertex set, with complemented distances across "
                    + "the copies. Any odd number of marked steps leads to the other copy of the "
                    + "starting vertex, at distance one."))),
                DescribeRole.Theorem))));
}
