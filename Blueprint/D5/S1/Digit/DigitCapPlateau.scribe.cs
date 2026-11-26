using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class DigitCapPlateauDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/DigitCapPlateau.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On each plateau (q-1)(ell+1)≤k≤q·ell-1 the count at (q-1) times a repunit is q^m "
            + "and the upper growth exponent is log q/log ell.",
        H("Plateaus of the bounded-digit upper growth exponent"),
        Blocks(
            Node("repunit", "Radix repunits", "repunitSum",
                "repunitSum ell m is the sum of ell^i over 0≤i≤m. It satisfies "
                + "ell^m≤repunitSum ell m and (ell−1)·repunitSum ell m+1=ell^(m+1).",
                DescribeRole.Definition),
            Node("count", "Exact count at scaled repunits", "count_plateau",
                "For natural ell, q, k and m with 2≤ell, 2≤q≤ell and "
                + "(q−1)(ell+1)≤k≤q·ell−1, count k ell ((q−1)·repunitSum ell m)=q^m. "
                + "For the lower bound, choose carries c(1),...,c(m) in {0,...,q−1} and "
                + "set c(0)=c(m+1)=0. The digits a(i)=(q−1)+ell·c(i+1)−c(i) for i≤m "
                + "are natural numbers at most (q−1)(ell+1)≤k, and the balance "
                + "a(i)+c(i)=(q−1)+ell·c(i+1), weighted by ell^i and summed, telescopes "
                + "to (q−1)·repunitSum ell m. The carries are recovered recursively from "
                + "the digits, so the q^m carry choices give distinct representations. "
                + "For the upper bound, (q−1)·repunitSum ell m≤(ell−1)·repunitSum ell m"
                + "<ell^(m+1), and the quotient-digit bound gives at most q^m "
                + "representations because k≤q·ell−1.", DescribeRole.Theorem),
            Node("exponent", "The exponent on a plateau", "exponent_plateau",
                "For natural ell, q and k with 2≤ell, 2≤q≤ell and (q−1)(ell+1)≤k≤q·ell−1, "
                + "the extended-real upper exponent of k at radix ell equals the real "
                + "number log q/log ell. For n≥2 with m=⌊log_ell n⌋, the quotient-digit "
                + "bound gives count k ell n≤q^m, while ell^m≤n, so the readout is at most "
                + "log q/log ell. At n=(q−1)·repunitSum ell m with m≥1 the count is q^m and "
                + "n<ell^(m+1), so the readout is at least m/(m+1)·log q/log ell. These "
                + "inputs are cofinal, so every tail supremum equals log q/log ell, and so "
                + "does the infimum over tails. In particular, when 2≤q≤ell−1 and "
                + "(q−1)(ell+1)≤k≤q·ell−2, the caps k and k+1 lie on the same plateau and "
                + "have equal exponents.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("digit-cap-plateau-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
