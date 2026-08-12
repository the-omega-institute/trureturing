using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.CertificateHistory;

internal sealed class FiniteCertificateDepthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every event-history certificate references only finitely many generating events.",
        H("Finite Certificate Depth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("every-certificate-references-finitely-many-generating-events"),
                DeclarationHandle.Create(
                    "D5/S0/CertificateHistory/FiniteCertificateDepth."
                    + "certificate_references_finitely_many_events"),
                H("Every certificate references finitely many generating events"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("c"), Sp, Colon, Sp,
                    Operatorname, Grp(F.Id("EventHistory")), Comma, Esc,
                    Operatorname, Grp(F.Id("Finite")), Open,
                    new Formula.SetBuilder(F.Id("u"), F.Id("u"), F.Id("c")),
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A certificate is represented by the repository's EventHistory carrier. "
                        + "The events referenced by the certificate are exactly those occurring "
                        + "in that history. Their underlying set is finite, with no additional "
                        + "finiteness premise on the certificate.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. The exact supporting result "
                        + "is List.finite_toSet, which states that the set of members of any list "
                        + "is finite. Since EventHistory is the list-based free monoid on Event, "
                        + "the Lean theorem is a one-line honest wrapper over that library result; "
                        + "it does not reprove list finiteness."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/History/HistoryCarrier"))]));
}
