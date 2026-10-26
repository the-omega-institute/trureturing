using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;
internal sealed class CountableSpectralMomentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Countable probability moments and the exact distinguished-coordinate identity.",
        H("Countable spectral moments"), Blocks(
            Paragraph(Text("For a nonnegative summable real sequence p, write m for its sum, q for the sum of its squares, and r for the sum of its cubes. The elementary symmetric moment e3 is the sum of p_i p_j p_k over i < j < k. There is no additional factorial in this convention. On subprobabilities every required series converges absolutely: squares and cubes are dominated by p, and the nonnegative partial triple sums are bounded by 1/6.")),
            Node("countable_newton", "Countable Newton identity",
                "The finite increasing-triple recurrence gives 6 e3 = m^3 - 3 m q + 2 r. Taking limits of the summable series proves the same identity on the entire countable domain."),
            Node("third_nonneg", "Nonnegative elementary symmetric moment",
                "Each increasing-triple summand is nonnegative. This observation supplies the remainder sign in the distinguished-coordinate exclusion."),
            Node("third_lower_of_purity_le_third", "The lower-purity branch",
                "For m = 1, summing p_i (p_i - q)^2 >= 0 gives r >= q^2. Newton's identity implies e3 >= (1 - 3q + 2q^2)/6. For 0 <= q <= 1/3 this expression is at least 1/27. The latter constant is not claimed to be the sharp bound at every smaller q."),
            Node("distinguished_identity", "An arbitrary distinguished coordinate",
                "Erase the coordinate x by putting zero in its original slot. The tail has mass 1-x, squared mass q-x^2 and cubic mass r-x^3. Applying Newton's identity to both sequences gives exactly e3(p)-1/32 = (2x-1)(4x-1)^2/32 + (x/2)(3/8-q) + e3(tail). The identity requires neither maximality of x nor any purity or sign restriction beyond the probability hypotheses."),
            Node("third_lower_of_distinguished_ge_half", "Conditional exclusion",
                "If x >= 1/2 and q <= 3/8, all three terms on the right of the exact identity are nonnegative, so e3 >= 1/32. Any distinguished coordinate meeting the hypothesis suffices; it need not be asserted maximal. This excludes a spectral region and gives no characterization of spectra realizable by a physical channel."))));
    private static DocumentBlock Node(string name, string title, string text) => Describe.Lean(
        DescribeId.Create("countable-spectral-" + name.Replace('_', '-')),
        DeclarationHandle.Create("D5/S3/Entropy/CountableSpectralMoments." + name),
        H(title), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
