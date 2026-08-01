using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class CompletionLedgerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Zeros/CompletionLedger",
            "Address independence exposes the completed-zeta factors as explicit global entries."),
        H("Completed Zeta Factors as Explicit Ledger Entries"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("the-completion-factors-are-address-independent-explicit-ledger-entries"),
                DescribeKind.Theorem,
                H("The completion factors are address-independent explicit ledger entries"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Zeros/CompletionLedger.completion_factors_are_explicit_ledger")),
                DescribeProvenance.RepoDerived(),
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
                LatexStatement.Create(
                    @"$$A(s)=\pi^{-s/2}\Gamma(s/2),\quad P(s)=s(s-1);\quad "
                    + @"A(s),P(s)\text{ are address-independent};\quad "
                    + @"\Re(s)>1\Rightarrow\Lambda(s)=A(s)\zeta(s);\quad "
                    + @"s\neq0,1\Rightarrow\xi(s)=\frac{1}{2}P(s)\Lambda(s)$$")))));
}
