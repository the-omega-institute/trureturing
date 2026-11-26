using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class DiagonalPadeResidueDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Polynomial/DiagonalPadeResidue.";
    private static readonly LibraryNoteRef Dlmf =
        LibraryNoteRef.Create("D5/L/Asymptotics/dlmf2010halfintbessel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reflected finite carrier determines the normalized residues at central Padé poles.",
        H("Central residues of the diagonal exponential Padé denominator"),
        Blocks(
            Node("residueAmplitudeLog", "Decaying amplitude logarithm",
                "The logarithm is Log F_K − (Log S)/2, with the principal logarithms of the "
                + "decaying amplitude F_K and of S(w) = sqrt(1+w²).",
                DescribeRole.Definition),
            Node("normalizedResidueLog", "Centered residue logarithm",
                "With Δ denoting the difference from a reference scaled pole, the exponent is "
                + "−ν ΔLog w + ν Δw − ν Δη + Δ residueAmplitudeLog.",
                DescribeRole.Definition),
            Node("exp_normalizedResidueLog", "Exact reflected residue ratio",
                "For two odd-order poles 2νw and 2νw₀, both scaled arguments have positive real "
                + "part and nonzero decaying amplitudes. Exponentiating the centered logarithm "
                + "gives R(2νw)/R(2νw₀). Reflecting the reversed denominator cancels the "
                + "alternating sign. The geometric residue uses the scale z^(2m+1), giving the "
                + "centered power term −ν ΔLog w.",
                DescribeRole.Theorem),
            Node("centralPole", "Pole at an integer phase",
                "The pole of index j for the inverse g is 2ν g(j π i/ν).",
                DescribeRole.Definition),
            Node("centralSummandExponent", "Exponent for a normalized summand",
                "For coefficient index n the summand exponent is the centered residue logarithm "
                + "minus n times the centered pole logarithm.",
                DescribeRole.Definition),
            Node("gaussianSummandExponent", "Gaussian exponent and signed phase",
                "Write 1/a = c/sqrt(1+c²), b = 1/sqrt(1+c²), D = c²/(2(1+c²)²), and τ = n/ν². "
                + "The exponent is −π² D τ j² + i j θ, where θ = π(1/a−b−1) − π b n/ν.",
                DescribeRole.Definition),
            Node("exists_central_residue_comparison", "Uniform central residue comparison",
                "At a positive zero c of η, a common cutoff and order threshold give distinct "
                + "central poles for all sufficiently large odd m. They include every pole whose "
                + "scaled argument lies in a fixed neighborhood of c. The index-zero pole r and "
                + "its residue W are positive real numbers. The centered residue logarithm is "
                + "analytic on the closed cutoff disk. Throughout the disk it differs from "
                + "ν(1/a−b−1)s by at most A(ν|s|²+|s|), and at s = j π i/ν its exponential is "
                + "the exact residue ratio. The corrected-phase derivative and the amplitude logarithm "
                + "on fixed disks control the error. For all n with τ in [1/4,1/2], the exact "
                + "normalized pole summand has an exponent which differs from the Gaussian "
                + "exponent by at most B(|j|+j²+|j|³)/ν. Every fixed finite range of indices "
                + "is included above a threshold independent of n. The same pointwise error "
                + "bounds the complex summands after exponentiation, since the exact and Gaussian "
                + "exponents lie in the closed left half-plane.",
                DescribeRole.Theorem),
            Node("exists_uniform_central_residue_truncation", "Uniform finite-sum comparison",
                "For each fixed J there is a common order threshold for every n in the closed "
                + "window and every finite set of integer indices with |j| ≤ J. The set indexes "
                + "distinct actual poles and uses the positive central normalization W r⁻ⁿ. "
                + "The norm of the difference between the two finite sums is at most B times "
                + "the number of indices divided by ν, where B depends on c and J.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("diagonal-pade-residue-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Dlmf), Blocks(Paragraph(Text(prose))), role);
}
