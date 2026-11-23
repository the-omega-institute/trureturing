using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeightedBond;

internal sealed class WeightedBondCountableColorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeightedBond/CountableColors.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/gonzalezdeleonwachs2026weighted");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite specialization of the countable-color sum.",
        H("Finite specialization of the countable-color sum"),
        Blocks(
            Node("CountableBond",
                "The connected-block model with natural-number colors. Each block has finite support and total weight its size minus one. Weights off blocks are zero.", DescribeRole.Definition),
            Node("childSum",
                "For a given vertex set and color, sum the weights of the partition blocks contained in that set.", DescribeRole.Definition),
            Node("Refines",
                "The partition refines the upper partition and each upper weight dominates the sum of the finer weights in that color.", DescribeRole.Definition),
            Node("pad",
                "Embed a finite color vector into the countable color model by filling the remaining coordinates with zeros.", DescribeRole.Definition),
            Node("pad_le_iff",
                "Zero-padding preserves and reflects the componentwise refinement order.", DescribeRole.Theorem),
            Node("lower_supported",
                "Every element below a padded element is supported on the same initial color segment.", DescribeRole.Theorem),
            Node("sum_range_cutoff",
                "Sums taken to two bounds agree when the summand vanishes from each bound onward.", DescribeRole.Theorem),
            Node("truncate",
                "For a countable weighting supported in the initial segment, restrict coordinates to that segment.", DescribeRole.Definition),
            Node("pad_truncate",
                "Zero-padding the truncation recovers the original supported weighting.", DescribeRole.Theorem),
            Node("padLowerIso",
                "Padding identifies the entire literal lower interval of a finite-color element with the entire countable-color lower interval below its image.", DescribeRole.Definition),
            Node("colorExponent",
                "The exponent of a color is the sum of that coordinate over the actual partition blocks.", DescribeRole.Definition),
            Node("colorExponent_finite",
                "There is a common cutoff from which every color exponent is zero.", DescribeRole.Theorem),
            Node("supported_iff_exponents",
                "The weights are supported below r if and only if every color exponent from r onward is zero.", DescribeRole.Theorem),
            Node("supportedColorsEquiv",
                "Finite-color elements are equivalent to the countable-color elements whose exponents vanish from r onward.", DescribeRole.Definition),
            Node("monomial_specializes",
                "For any support cutoff, substituting X below r and zero from r onward gives X to the rank on supported elements and zero on the others.", DescribeRole.Theorem),
            Node("sourceMu",
                "Take the incidence Möbius value from bottom to top in the element's literal countable-color lower interval. That interval is finite by the top's finite color support.", DescribeRole.Definition),
            Node("sourceMu_pad",
                "The Möbius value of a padded element in the countable-color lower interval equals its original Möbius value in the finite-color poset.", DescribeRole.Theorem),
            Node("sourceMonomial",
                "Specialize the color monomial at X on the initial segment of r colors and at zero on the remaining colors, using a finite product up to an exponent cutoff.", DescribeRole.Definition),
            Node("sourceSpecialization",
                "Sum the specialized monomials over the countable-color poset of the complete graph, with the integer coefficients from its actual lower intervals.", DescribeRole.Definition),
            Node("sourceSpecialization_eq",
                "The specialized countable-color sum in equation (7.1) is the finite-color rank polynomial, for every vertex count and color count.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string name, string prose, DescribeRole role, Formula? formula = null,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
            H(name), formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, resolution);
}
