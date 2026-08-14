using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.DescriptionComplexity;

internal sealed class AffordableRegionAgreementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An affordable finite-region patch forces agreement for a loss-minimal candidate.",
        H("Affordable Region Agreement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("affordable-region-agreement"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/DescriptionComplexity/AffordableRegionAgreement.affordable_region_agreement"),
                H("Affordable regions contain no remaining disagreement"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("price")), Open, F.Id("P"), Close,
                    Sp, Leq, Sp, F.Id("budget"), Sp, Minus, Sp,
                    Operatorname, Grp(F.Id("complexity")), Open, F.Id("g"), Close,
                    Sp, Minus, Sp, F.Id("overhead"), Sp, Rightarrow, Sp,
                    Forall, Sp, F.Id("n"), Sp, InMacro, Sp, F.Id("P"),
                    Comma, Esc, F.Id("g"), Open, F.Id("n"), Close,
                    Sp, Eq, Sp, Operatorname, Grp(F.Id("truth")),
                    Open, F.Id("n"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The candidate and truth are total functions on the natural numbers. "
                        + "A finite record fixes their observed values, while a finite region P "
                        + "specifies the values replaced by the truth function.")),
                    Paragraph(Text(
                        "The patch-cost premise bounds the corrected function by the candidate "
                        + "complexity plus price(P) and a fixed overhead. The accounting premise "
                        + "makes the natural-number subtraction explicit, so an affordable patch "
                        + "remains within the stated budget and stays consistent with the record.")),
                    Paragraph(Text(
                        "Loss is valued in an arbitrary preorder. Correcting a genuine disagreement "
                        + "on a nonempty region, while changing nothing outside it, is assumed to "
                        + "strictly lower loss. This contradicts candidate minimality among all "
                        + "record-consistent functions within budget, forcing pointwise agreement.")),
                    Paragraph(Text(
                        "Pinned Mathlib has no universal-machine or description-complexity theorem "
                        + "with these semantics. The proof therefore exposes cost and loss behavior "
                        + "as hypotheses and reuses only finite-set patching, natural arithmetic, "
                        + "and preorder contradiction."))),
                DescribeRole.Theorem)),
        []));
}
