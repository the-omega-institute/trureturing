using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SieveCorrelationAssemblyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full interval correlations from finite sieve inputs",
        H("Full interval correlations from finite sieve inputs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("interval-correlations-of-sieve-inputs"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCorrelationAssembly.interval_correlations_of_sieve_inputs"),
                H("interval correlations of sieve inputs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assuming the Montgomery–Soundararajan square-sum asymptotic (MSSecond, a consequence of their Theorem 2 and equation (16)) and the finite-sieve interval third-moment and fourth Wick-defect conclusions (FiniteSieveIntervals, the conclusion of Lemma 498.3(c) for Q = primorial(floor(((M+5)H)^10))), the full singular series satisfies the interval correlation estimates (498.6)–(498.7). The primorial-family conclusion is assumed here; its derivation from Montgomery–Soundararajan Theorem 1 and Kuperberg Theorem 1.3 is not proved here. The second correlation has the overlap main term with error O(H); the third correlations, fourth Wick defects and fourth leading-term errors share one nonnegative error modulus, antitone on [2,infinity) and tending to zero. Combined with fixed_scale_third and fixed_scale_fourth, this yields §497’s (F₃)/(F₄) for ψ − id under HL₄(β), for 0 < θ < β < 1/4. Chinese-remainder moments and quantitative Euler tails provide part (b); the quadratic identities with coefficients P-2 and P-1 remove coincident indices in part (d)."))),
                DescribeRole.Theorem))));
}
