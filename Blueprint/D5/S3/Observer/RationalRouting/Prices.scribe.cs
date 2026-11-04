using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.RationalRouting;

internal sealed class PricesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every exact original view has acquired action price two and preset action price four.",
        H("Exact original-view action prices"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-rational-view-action-prices"),
                DeclarationHandle.Create("D5/S3/Observer/RationalRouting/Prices.original_view_action_prices"),
                H("One prior and both controller classes"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The five targets are separately the exact original rational B, its entire chronological word T, its rooted oriented named-edge path S, its indexed prefix-pair table M and the joint full output. The prior includes both c_0=1/6 and c_1=2/3 and all c_i-1/n for every integer n at least 12. Every action and nondisturbing dyadic floor read is executed on one current source. Common initialization and a source-independent instruction function rule out exact unknown input and unknown source advice.")),
                    Paragraph(Text("For each target the conjunction states feasibility at acquired cap 2, that every feasible acquired cap is at least 2, feasibility at preset cap 4, and that every feasible preset cap is at least 4. Feasibility quantifies over arbitrary deterministic state and instruction functions and arbitrary common preset schedules, a class containing ordinary finite controllers. The attaining source-dependent decisions are made by the explicit finite acquisition code, and the only added calculation maps its recovered rational to the requested whole original output. This calculation preserves every physical action, actual read and stopping cut and is finite even when the original word and table are long.")),
                    Paragraph(Text("The finite actual-image decoders make each target injective on the prior. Consequently the universal finite-run replay and incompatible short routes apply to each one. Conversely, the actual two-mode rational acquisition and finite original-view construction attain the stated caps. Preset acquisition follows the single word LLRL and may stop after its first LL on the lower band. Adaptive scales and early stopping are included in that opponent class.")),
                    Paragraph(Text("Only the uniform new-source action coordinate is minimized. The proof gives no uniform bound or optimum for read counts, scale encodings, local arithmetic, transient or retained memory, service work or complete output length. The services are conditional exact, noiseless, unclipped and finite-completing ports; no physical implementation or noise tolerance is asserted."))),
                DescribeRole.Theorem))));

    private static Formula Statement() => Disp(Seq(
        Forall, Sp, F.Id("V"), InMacro, OpenBrace, F.Id("B"), Comma, F.Id("T"), Comma,
        F.Id("S"), Comma, F.Id("M"), Comma, Open, F.Id("B"), Comma, F.Id("T"), Comma, F.Id("S"), Comma, F.Id("M"), Close, CloseBrace, Comma, Sp,
        Call("FeasibleRec", F.Id("V"), D(2)), Land, Sp,
        Open, Forall, Sp, F.Id("h"), Comma, Call("FeasibleRec", F.Id("V"), F.Id("h")), Longrightarrow, D(2), Leq, Sp, F.Id("h"), Close,
        Land, Sp, Call("FeasiblePre", F.Id("V"), D(4)), Land, Sp,
        Open, Forall, Sp, F.Id("h"), Comma, Call("FeasiblePre", F.Id("V"), F.Id("h")), Longrightarrow, D(4), Leq, Sp, F.Id("h"), Close));
}
