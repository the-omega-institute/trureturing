using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ActualOddHarmonicMobiusTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unconditional arithmetic bounds the actual odd harmonic Mobius prefix and pays its complete finite declining-weight tail with the exact signed anchor.",
        H("Actual Odd Harmonic Mobius Tails"),
        Blocks(
            Paragraph(Text(
                "H(N) is the existing PrimePrefixMobiusDirectedAbel.harmonicPrefix: "
                + "the inclusive positive sum of mu(n)/n. Ho(N) restricts the same "
                + "actual Mathlib Mobius coefficients to odd n. W(D,M,b) sums "
                + "mu(n)b(n)/n over odd D<n<=M; all divisions in coefficients "
                + "are real, while N/2 in the dyadic recurrence is natural division.")),
            Describe.Lean(
                DescribeId.Create("actual-odd-harmonic-mobius-tail"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualOddHarmonicMobiusTail.result"),
                H("Unconditional prefixes and complete anchored finite tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural cutoff, abs(H(N))<=1 and abs(Ho(N))<=2. "
                        + "The empty prefixes are zero, and the unit is retained "
                        + "exactly: Ho(1)=1. Mathlib's sum_Ioc_mul_zeta_eq_sum and "
                        + "coe_moebius_mul_coe_zeta give sum mu(n)*floor(N/n)=1 "
                        + "for N>=1. Therefore N*H(N)=1+sum mu(n)*(N/n-floor(N/n)). "
                        + "The fractional term at n=1 is exactly zero; each of "
                        + "the other N-1 terms has absolute value at most one. "
                        + "This proves the full harmonic bound without RH or PNT.")),
                    Paragraph(Text(
                        "The original weighted_split is exposed at "
                        + "ActualOddMobiusFinitePairing, together with its "
                        + "oddCoefficient. Its proof and provenance stay at that "
                        + "owner. Applying it to weight 1/n gives "
                        + "Ho(N)=H(N)+Ho(floor(N/2))/2. Strong induction pays the "
                        + "uniform odd bound. The unweighted summatory function "
                        + "is never substituted for a harmonic prefix.")),
                    Paragraph(Text(
                        "For every D<M, W=b(M)*(Ho(M)-Ho(D)) plus the sum over "
                        + "D<n<=M-1 of (b(n)-b(n+1))*(Ho(n)-Ho(D)). "
                        + "The terminal coefficient is included. This directly "
                        + "uses the generic anchored_sum_by_parts extracted at "
                        + "PrimePrefixMobiusDirectedAbel, whose original full "
                        + "harmonic theorem and statement remain intact. Its "
                        + "existing source attribution and license continue "
                        + "to apply to the extracted Abel algebra.")),
                    Paragraph(Text(
                        "When b is nonnegative and antitone on [D+1,M], "
                        + "(-2-Ho(D))*b(D+1)<=W<=(2-Ho(D))*b(D+1), and "
                        + "abs(W)<=4*b(D+1). The increments and terminal "
                        + "coefficient are nonnegative and sum exactly to "
                        + "b(D+1). The unconditional arithmetic supplier is "
                        + "on the proof path; no odd-prefix bound is assumed.")),
                    Paragraph(Text(
                        "The finite tail is a substantive consumer of the "
                        + "arithmetic bounds. This is a classical elementary "
                        + "estimate, with no mathematical priority claim. "
                        + "Ordinary infinite signed convergence, the actual "
                        + "factorial weight's positivity, monotonicity and "
                        + "decay, the final Robin sign and RH remain obligations. "
                        + "No absolute summability is asserted."))),
                DescribeRole.Theorem))));
}
