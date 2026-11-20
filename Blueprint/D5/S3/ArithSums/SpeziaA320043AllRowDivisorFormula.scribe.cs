using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class SpeziaA320043AllRowDivisorFormulaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/SpeziaA320043AllRowDivisorFormula.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026a320043squares");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every N ≥ 1 the A320043 row sum satisfies 12 a(N − 1) = ∑_{m ∣ N} "
            + "(m³φ(m) − m²E(m)), with E(m) = ∏_{q ∣ m prime} (1 − q).",
        H("The all-row divisor formula for A320043"),
        Blocks(
            Describe.Lean(DescribeId.Create("spezia-a320043-all-row-e"),
                DeclarationHandle.Create(Prefix + "E"),
                H("The prime-factor product E"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "E(m) = ∏_{q ∣ m, q prime} (1 − q), with E(1) = 1 as the empty product."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("spezia-a320043-all-row-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Exact quotients and the divisor formula"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Every quotient (n + 1 − k)²k/gcd(n + 1 − k, k)³ in a(n) is exact, and for "
                    + "every N ≥ 1, 12 a(N − 1) = ∑_{m ∣ N} (m³φ(m) − m²E(m)); at N = 1 both "
                    + "sides vanish. Grouping 1 ≤ k < N by g = gcd(k, N) writes k = j·(N/m) with "
                    + "m = N/g dividing N and j coprime to m, so a(N − 1) = ∑_{m ∣ N} S(m) with "
                    + "S(m) = ∑_{1≤j<m, (j,m)=1} (m − j)²j. The same grouping gives "
                    + "∑_{1≤k<m} (m − k)²k = ∑_{d ∣ m} (m/d)³ S(d), and telescoping evaluates the "
                    + "left side as (m⁴ − m²)/12. The candidate values (m³φ(m) − m²E(m))/12 satisfy "
                    + "the same relation, because ∑_{d ∣ m} φ(d) = m and ∑_{d ∣ m} (m/d)E(d) = 1; "
                    + "the latter holds since both sides are multiplicative and agree on prime "
                    + "powers. Strong induction on m then gives 12 S(m) = m³φ(m) − m²E(m). This is "
                    + "Corollary 7 of H. Ma and W. Zhang's note on A320043 "
                    + "(DOI 10.5281/zenodo.24058057)."))),
                DescribeRole.Theorem))));
}
