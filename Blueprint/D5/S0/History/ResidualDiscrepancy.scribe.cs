using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History;

internal sealed class ResidualDiscrepancyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A discrepancy is residual exactly when observed and expected readings differ.",
        H("Residual Discrepancies"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-residual-discrepancy-is-a-nonzero-difference"),
                DeclarationHandle.Create("D5/S0/History/ResidualDiscrepancy.residual_iff_observed_ne_expected"),
                H("A residual discrepancy is a nonzero difference"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("IsResidual")),
                    Open, F.Id("expected"), Comma, Sp, F.Id("observed"), Close,
                    Sp, Iff, Sp,
                    F.Id("observed"), Sp, Neq, Sp, F.Id("expected")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For readings in any additive group, the residual discrepancy is "
                        + "the observed value minus the expected value. It is residual "
                        + "exactly when that difference is nonzero. The theorem therefore "
                        + "identifies the source atom's residual condition with the direct "
                        + "statement that the two readings differ; no order, norm, or "
                        + "numeric representation is assumed.")),
                    Paragraph(Text(
                        "Adding the expected reading back on the right of the difference "
                        + "recovers the observed reading. If the difference vanishes, that "
                        + "recovery forces both readings to agree. Equal readings give zero "
                        + "by the inverse law."))),
                DescribeRole.Theorem))));
}
