using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History;

internal sealed class EmptyLedgerConservationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete detection discipline makes an empty open ledger exclude detectable residuals.",
        H("Empty Ledger Conservation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("empty-ledger-excludes-detectable-residuals"),
                DeclarationHandle.Create("D5/S0/History/EmptyLedgerConservation.empty_ledger_excludes_detectable_residual"),
                H("An empty open ledger excludes detectable residuals"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open,
                    Forall, Sp, F.Id("x"), Comma, F.Id("r"), Comma, Esc,
                    Operatorname, Grp(F.Id("detectable")), Open, F.Id("x"), Comma,
                    F.Id("r"), Close, Rightarrow, Sp, F.Id("r"), InMacro, Sp,
                    Operatorname, Grp(F.Id("OpenLedger")), Open, F.Id("x"), Close,
                    Close, Esc, Land, Esc,
                    Operatorname, Grp(F.Id("OpenLedger")), Open, F.Id("x"), Close,
                    Eq, Emptyset, Rightarrow, Sp, Neg, Exists, Sp, F.Id("r"), Comma,
                    Esc, Operatorname, Grp(F.Id("detectable")), Open, F.Id("x"),
                    Comma, F.Id("r"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Detection discipline requires every residual that can be detected "
                        + "at an object to occur in that object's open ledger. If the open "
                        + "ledger is empty, a detectable residual would therefore supply an "
                        + "element of the empty set, which is impossible. The conclusion is "
                        + "conditional on the discipline hypothesis; it does not claim that "
                        + "all residuals are detectable or that detection is decidable.")),
                    Paragraph(Text(
                        "The library search found the exact set-theoretic core in pinned "
                        + "Mathlib as `Set.eq_empty_iff_forall_notMem`. The formal theorem is "
                        + "a thin honest wrapper: that equivalence converts the empty-ledger "
                        + "hypothesis into pointwise non-membership, while discipline turns "
                        + "a hypothetical detectable residual into the forbidden membership. "
                        + "No separate ledger implementation or detection algorithm is "
                        + "introduced."))),
                DescribeRole.Theorem))));
}
