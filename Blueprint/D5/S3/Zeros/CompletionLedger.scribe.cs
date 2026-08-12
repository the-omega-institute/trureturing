using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class CompletionLedgerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Zeros/CompletionLedger",
            "Address independence exposes the completed-zeta factors as explicit global entries."),
        H("Completed Zeta Factors as Explicit Ledger Entries"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-completion-factors-are-address-independent-explicit-ledger-entries"),
                DeclarationHandle.Create("D5/S3/Zeros/CompletionLedger.completion_factors_are_explicit_ledger"),
                H("The completion factors are address-independent explicit ledger entries"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("A"), Open, F.Id("s"), Close, Eq, Pi, Caret, Grp(Minus, F.Id("s"), Slash, D(2)), Gamma, Open, F.Id("s"), Slash, D(2), Close, Comma, Quad, Sp, F.Id("P"), Open, F.Id("s"), Close, Eq, F.Id("s"), Open, F.Id("s"), Minus, D(1), Close, Semi, Quad, Sp, F.Id("A"), Open, F.Id("s"), Close, Comma, F.Id("P"), Open, F.Id("s"), Close, F.Text, Grp(Sp, F.Id("are"), Sp, F.Id("address"), Minus, F.Id("independent")), Semi, Quad, Sp, Re, Open, F.Id("s"), Close, Gt, D(1), Rightarrow, Lambda, Open, F.Id("s"), Close, Eq, F.Id("A"), Open, F.Id("s"), Close, Zeta, Open, F.Id("s"), Close, Semi, Quad, Sp, F.Id("s"), Neq, D(0), Comma, D(1), Rightarrow, Xi, Open, F.Id("s"), Close, Eq, Frac, Grp(D(1)), Grp(D(2)), F.Id("P"), Open, F.Id("s"), Close, Lambda, Open, F.Id("s"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "只形式化 23.2 被 23.7 使用的 a-无关充分方向;\"未入账\"/\"显式全局 ledger\"本体判据留叙事层。")),
                                    Paragraph(Text(
                                        "The theorem defines the archimedean factor and pole-removal factor only "
                                        + "through proposition-local lets. For arbitrary ledger and address types, "
                                        + "a supplied ledger value, and any two addresses, both constant coordinate "
                                        + "lifts agree. On the half-plane with real part greater than one, the "
                                        + "completed reading is the archimedean factor times classical zeta. Away "
                                        + "from zero and one, the xi reading is one half times the pole-removal "
                                        + "factor times the completed reading. The analytic equalities reuse the "
                                        + "existing Mellin reconstruction and pole-cancellation theorems."))),
                DescribeRole.Theorem
            )),
[
                        DocumentEdge.Dependency.Create(
                            GidRef.Create("D5/S3/Analytic/CompletedZetaMellinReconstruction")),
                    ]));
}
