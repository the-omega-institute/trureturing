using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Irrationality;

internal sealed class LogPrimeRatioIrrationalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LogPrimeRatioIrrationality",
        H("D5 and Reg sources compile; RegUNVALIDATED audit"),
        Blocks(
            Paragraph(Text("The D5 and Reg source targets compile under the scoped Lean checks. The retained Reg sources compile with standard axiom closure; the escape audit remains incomplete for lawful enrollment and source binding; no novelty or consensus claim is asserted. Ordinary Pro reasoning is fallible input. These components feed the separate actual two/four paid-prefix repair. The uniform original-price and optional elementary-energy endgoals remain open. Existing owners are imported with visibility-only consumed-helper exposures. Each public target has a faithful full-telescope typed Reg attempt; rejected lawful families, whole-family variation, sensitivity, observational dependence and exact source binding remain missing.")),
            Describe.Lean(
                DescribeId.Create("logprimeratioirrationality-irrational-log-three-div-log-two"),
                DeclarationHandle.Create("D5/S3/Constants/Irrationality/LogPrimeRatioIrrationality.irrational_log_three_div_log_two"),
                H("irrational log three div log two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean telescope: theorem irrational_log_three_div_log_two : Irrational (log 3 / log 2)"))),
                DescribeRole.Theorem)
        )));
}
