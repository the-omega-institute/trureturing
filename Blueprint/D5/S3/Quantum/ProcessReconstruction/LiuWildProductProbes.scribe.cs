using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class LiuWildProductProbesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/LiuWildProductProbes";
    private static readonly LibraryNoteRef LiuWild =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/liuwild2026localtomography");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fresh product inputs yield exponentially small per-call separation of two explicit channels.",
        H("Optimal Adaptive Product Probes for an Explicit Channel Pair"),
        Blocks(
            Paragraph(Text(
                "The testing curve holds for n ≥ 1 qubits. Each channel has Kraus rank two for n ≥ 2. "
                + "The two channels induce identical reduced maps on every proper output subset, "
                + "even with a retained reference. A full-output measurement on a GHZ input "
                + "distinguishes them in one call.")),
            Describe.Lean(DescribeId.Create("product-probe-one-call"),
                DeclarationHandle.Create(Module + ".product_probe_totalVariation_le"),
                H("One-call total variation with any global output measurement"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "A fresh mixed product input creates at most 2/2ⁿ variation between the "
                    + "outcome laws for the two channels, for any finite measurement on the full "
                    + "output. The matrix entry joining the two antipodal words factors over the sites."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("adaptive-product-probe-success"),
                DeclarationHandle.Create(Module + ".liu_wild_product_input_worst_case_success_le"),
                H("Sharp worst-case success after a fixed number of calls"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "For each of M calls, the policy chooses a fresh tensor product of single-qubit "
                    + "density states and a finite POVM on that call’s full output. The choices use "
                    + "only the classical history and a finite seed with the same law under both "
                    + "hypotheses. The worst-case success is at most "
                    + "1 − (1 − 2/2ⁿ)^M/2. Success of at least two thirds requires "
                    + "at least 2ⁿ/6 calls."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("adaptive-product-probe-attainment"),
                DeclarationHandle.Create(Module + ".liu_wild_product_input_success_attained"),
                H("Repeated all-plus probes attain the bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "The three-outcome measurement projects onto the two antipodal GHZ "
                    + "directions and their orthogonal complement. The correct conclusive "
                    + "outcome has probability 2/2ⁿ. If every call is inconclusive, a shared "
                    + "fair random bit guesses the channel. This protocol attains the bound "
                    + "on each channel."))),
                DescribeRole.Theorem))));
}
