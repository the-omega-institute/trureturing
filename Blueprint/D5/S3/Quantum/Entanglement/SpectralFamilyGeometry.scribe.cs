using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class SpectralFamilyGeometryDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Quantum/Entanglement/SpectralFamilyGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite coordinate probability families have an attained variance maximum and a simplex support certificate, including sorted residual spectra.",
        H("Geometry of a Finite Spectral Family"),
        Blocks(
            Paragraph(Text(
                "Let S be any nonempty finite sector type and C any finite coordinate type. "
                + "Each spectrum q(s) is a nonnegative real function on C with coordinate sum one. "
                + "The weight p is a real function on S; the standard simplex consists of the "
                + "nonnegative weights whose sum is one. Write B(s,t) for the Bhattacharyya "
                + "overlap, the sum over C of sqrt(q(s,j) q(t,j)). Write H(s,t) for the "
                + "squared Hellinger gap, the sum of squared differences of the coordinate "
                + "square roots. No distinctness or invertibility assumption is imposed.")),
            Paragraph(Text(
                "This coordinatewise probability-family statement applies to residual spectra "
                + "after sorting them in a common decreasing coordinate order and padding them "
                + "with zeros. It also allows unsorted coordinate functions. In that larger "
                + "domain, equality and zero gap compare the coordinate functions themselves, "
                + "rather than spectra up to independent permutations.")),
            Describe.Lean(
                DescribeId.Create("spectral-gram-energy"),
                DeclarationHandle.Create(DeclarationPrefix + "spectralGramEnergy"),
                H("Spectral Gram energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "G(p) is the sum over ordered sector pairs (s,t) of p(s) p(t) B(s,t). "
                    + "It is the squared norm of the weighted sum of square-root spectra."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("spectral-pair-variance"),
                DeclarationHandle.Create(DeclarationPrefix + "spectralPairVariance"),
                H("Pairwise spectral variance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "V(p) is the sum over ordered sector pairs (s,t) of p(s) p(t) H(s,t). "
                    + "The ordered-pair convention makes the two opposite cross terms both count."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("spectral-gap"),
                DeclarationHandle.Create(DeclarationPrefix + "spectralGap"),
                H("Spectral gap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The gap of sectors s and t is H(s,t), the squared Euclidean distance "
                    + "between their coordinatewise square-root spectra."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-spectral-family-geometry"),
                DeclarationHandle.Create(DeclarationPrefix + "finite_spectral_family_geometry"),
                H("Maximum variance and simplex support certificate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every simplex weight p, V(p)=2(1-G(p)). There are a simplex "
                        + "weight p* and sectors s,t such that p* maximizes V over the whole "
                        + "simplex, H(s,t) is at least every sector-pair gap, and "
                        + "H(s,t)/2 <= V(p*) <= H(s,t).")),
                    Paragraph(Text(
                        "The maximum V(p*) vanishes exactly when all sector spectra coincide. "
                        + "For every sector a, G(p*) is at most the p*-weighted overlap row "
                        + "sum B(a,t); equality holds whenever p*(a)>0. For every "
                        + "simplex weight r, minimizing G over the whole simplex is "
                        + "equivalent to every overlap row sum being at least G(r), "
                        + "with equality at every sector a where r(a)>0.")),
                    Paragraph(Text(
                        "The Gram energy is a sum of coordinate squares. This positive "
                        + "semidefinite identity gives the converse certificate; a "
                        + "one-sided perturbation toward each simplex vertex gives the "
                        + "necessary inequalities. The two endpoint weights establish the "
                        + "diameter lower bound even when the endpoints coincide."))),
                DescribeRole.Theorem))));
}
