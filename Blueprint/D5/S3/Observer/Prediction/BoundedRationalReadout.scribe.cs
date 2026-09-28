using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Prediction;

internal sealed class BoundedRationalReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniformly accurate rational readouts with separate storage bounds.",
        H("Bounded rational readout"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniform-tail-clip-error-and-bit-budget"),
                DeclarationHandle.Create("D5/S3/Observer/Prediction/BoundedRationalReadout."
                    + "uniform_tail_clip_error_and_bit_budget"),
                H("Clipping with retained integer evidence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A finite binary report history has balance b equal to its "
                        + "number of ones minus its number of zeros. The empty balance is zero; "
                        + "each new one adds one and each new zero subtracts one. The exact "
                        + "readout is f(b) = 1/4 + 3^b / (2(1+3^b)). Fix a real tolerance "
                        + "0 < epsilon < 1/4 and an integer K at least one with "
                        + "delta_K = 1/(2(1+3^K)) at most epsilon. The clipped readout g_K "
                        + "equals 1/4 for b at most -K, f(b) for -K < b < K, and 3/4 "
                        + "for b at least K. The full balance remains the evolving state.")),
                    Paragraph(Text("The symmetry f(-b) = 1-f(b) gives both tails. On the "
                        + "positive tail, 3/4-f(b) equals 1/(2(1+3^b)), lies between zero "
                        + "and delta_K, and includes equality at b=K. On the negative tail, "
                        + "f(b)-1/4 equals 1/(2(1+3^(-b))) and has the same bounds. "
                        + "Interior values incur zero error. Consequently every finite "
                        + "history, including the empty history, has error at most epsilon.")),
                    Paragraph(Text("Write n=|b|. An interior value has the unreduced "
                        + "positive-denominator fraction (1+3^(n+1))/(4(1+3^n)) when "
                        + "b is nonnegative, and (3^n+3)/(4(1+3^n)) when b is negative. "
                        + "Tail values use 1/4 and 3/4. Each numerator and denominator "
                        + "has at most 2K+4 binary digits. The literal interior table "
                        + "has 2K-1 entries, indexed in increasing balance order from "
                        + "-K+1 to K-1. Two fixed fields of width 2K+4 per entry use "
                        + "(2K-1)(4K+8) bits, at most 24K^2.")),
                    Paragraph(Text("At report time t, the balance has magnitude at most t. "
                        + "A sign bit and its binary magnitude require at most "
                        + "2+floor(log_2(t+1)) bits, also covering t=0. These are separate "
                        + "bounds for the dynamic balance, the static literal table, "
                        + "and the output fractions. No running-time, comparison, lookup, "
                        + "temporary-work or total-program-space bound is asserted; "
                        + "neither uniqueness nor optimality of this representation is required.")),
                    Paragraph(Text("The clipped value alone cannot retain the evidence "
                        + "needed for future reports. Equal-length histories can have "
                        + "balances K and K+2n, hence the same clipped output 3/4. "
                        + "A common continuation of K+n zeros leaves balances -n and n. "
                        + "For sufficiently large n, the two target values differ by "
                        + "more than twice epsilon. No forecast based only on the current "
                        + "clipped value, the public history length and the continuation "
                        + "length can approximate both. Even exact one-step updating "
                        + "of g_K from g_K alone fails: balances K and K+1 have identical "
                        + "outputs, but one zero sends them to different outputs."))),
                DescribeRole.Theorem)),
        []));
}
