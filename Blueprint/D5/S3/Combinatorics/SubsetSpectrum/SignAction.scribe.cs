using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SubsetSpectrum;

internal sealed class SignActionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SubsetSpectrum/SignAction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Even zero-sum sign changes and coordinate permutations preserve even subset spectra.",
        H("Sign changes on index occurrences"),
        Blocks(
            Describe.Lean(DescribeId.Create("flip-coefficients"),
                DeclarationHandle.Create(Prefix + "flipCoefficients"), H("Flip an index set"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient at i is negated precisely when i belongs to I."))),
                DescribeRole.Definition),
            Theorem("even-zero-flip", "even_zero_flip_preserves_spectrum", "Even zero-sum flips",
                "If I has even cardinality and its original coefficients sum to zero, flipping "
                + "the coefficients on I preserves the even occurrence spectrum. Symmetric "
                + "difference with I bijects the even index subsets; the subset-sum identity "
                + "subtracts the sum over I, which vanishes."),
            Theorem("permutation", "even_spectrum_permutation", "Permutation of occurrences",
                "Reindexing by any coordinate permutation preserves the even occurrence spectrum. "
                + "The induced bijection acts on index subsets, without identifying equal coefficient values."),
            Theorem("sign-permutation-converse", "even_spectrum_of_sign_permutation",
                "The sign-permutation condition is sufficient",
                "For any natural m and arbitrary real families b,c on Fin m, suppose a permutation "
                + "sigma and an even index set I satisfy sum_I b = 0 and c(sigma i) equals -b(i) "
                + "on I and b(i) off I. Then their even occurrence spectra coincide. This implication "
                + "includes zero and repeated coefficients and holds without a parity restriction on m."),
            Theorem("odd-flip", "odd_zero_flip_interchanges_spectra", "Odd zero-sum flips exchange parity",
                "If the zero-sum flip set has odd cardinality, symmetric difference carries "
                + "even index subsets to odd index subsets. The even spectrum after the flip "
                + "therefore equals the original odd spectrum, with multiplicities preserved."),
            Theorem("parity-obstruction", "even_ne_odd_of_nonzero", "The minimum distinguishes parity",
                "If every coefficient is nonzero, the even and odd spectra are unequal. "
                + "The subset of precisely the negative coefficients is the unique subset "
                + "attaining the full minimum: equality in the coordinatewise lower bound "
                + "forces every membership decision. Its sum can occur in only one parity."),
            Theorem("flip-parity-or-zero", "sign_set_even_or_zero", "The obstruction to an odd flip",
                "If a zero-sum sign flip preserves the even spectrum, either its index set "
                + "has even cardinality or some original coefficient is zero. An odd flip "
                + "would identify the even and odd spectra, contradicting the unique minimum "
                + "when all coefficients are nonzero."),
            Theorem("repair-flip-parity", "repair_flip_parity", "Repair flip parity using a zero coordinate",
                "For any zero-sum flip preserving the even spectrum, there is an even "
                + "zero-sum flip with the same resulting coefficient family. If the original "
                + "flip has odd cardinality, the parity obstruction supplies a zero coordinate. "
                + "Inserting or removing that coordinate changes the flip cardinality by one, "
                + "while preserving both the coefficient family and the zero sum."),
            Definition("negative-indices", "negativeIndices", "Negative coefficient indices",
                "The negative indices are precisely the coordinates with strictly negative coefficient."),
            Definition("negative-mass", "negativeMass", "Negative mass",
                "The negative mass is the sum of the strictly negative coefficients."),
            Theorem("signed-normalization", "full_spectrum_signed_normalization", "Signed normalization",
                "The full spectrum is the full spectrum of the absolute coefficients translated "
                + "by the negative mass. Symmetric difference with the negative index set "
                + "bijects all index subsets, preserving every occurrence including those caused by zeros."),
            Theorem("full-minimum", "full_spectrum_minimum", "The least full subset sum",
                "The negative mass is the least value in the full occurrence spectrum. Every "
                + "coordinate is minimized by including a negative coefficient and omitting a positive "
                + "one; zero coefficients may be included or omitted."),
            Theorem("absolute-reduction", "even_spectrum_absolute_reduction", "Reduction to absolute coefficients",
                "For odd m at least three, equal even spectra imply equal coefficient totals, "
                + "equal negative masses, and equal full occurrence spectra of the absolute coefficients. "
                + "The minimum determines the translation in signed normalization; injectivity of "
                + "translation then cancels it."),
            Theorem("absolute-permutation-to-even-flip", "even_sign_witness_of_absolute_permutation",
                "Recover the even sign witness from an occurrence matching",
                "For odd m at least three, let b,c have equal even spectra and let sigma "
                + "match the absolute values of their coefficient occurrences. Then the same "
                + "sigma admits an even zero-sum flip set I with c(sigma i) equal to -b(i) "
                + "on I and b(i) off I. Equal totals force the initial flip sum to vanish; "
                + "the zero-coordinate construction repairs its parity when necessary.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SubsetSpectrum/EvenBridge"))]));

    private static DocumentBlock Definition(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
