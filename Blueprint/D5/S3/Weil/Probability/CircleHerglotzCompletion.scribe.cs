using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability;

internal sealed class CircleHerglotzCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Probability/CircleHerglotzCompletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Circle probability measures, the existing negative-power Fourier moments, and the existing Toeplitz matrices.",
        H("CircleHerglotzCompletion"),
        Blocks(
            Describe.Lean(DescribeId.Create("circlemoment-continuous"),
                DeclarationHandle.Create(Prefix + "circleMoment_continuous"), H("Weak continuity of each original moment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same negative-power circle moment is continuous on the actual weak probability-measure space."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("circle-moment-ext"),
                DeclarationHandle.Create(Prefix + "circle_moment_ext"), H("All original moments determine the measure"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transport the existing AddCircle Fourier uniqueness theorem through the standard circle homeomorphism, retaining the sign convention."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hermitian-of-all-toeplitz"),
                DeclarationHandle.Create(Prefix + "hermitian_of_all_toeplitz"), H("Hermitian symmetry is derived"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Matrix entries at each positive and negative index force conjugation symmetry; no symmetry premise is added."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("circle-herglotz-exists"),
                DeclarationHandle.Create(Prefix + "circle_herglotz_exists"), H("One common measure for every finite order"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing finite atomic representations give nested nonempty closed subsets of a compact probability-measure space. Their intersection supplies all moments at once."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("circle-herglotz-iff"),
                DeclarationHandle.Create(Prefix + "circle_herglotz_iff"), H("Normalized Toeplitz positivity characterizes a unique measure"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Normalization is explicit. The existence conclusion includes uniqueness of the actual Borel probability measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("continuous-iff-circlemoments"),
                DeclarationHandle.Create(Prefix + "continuous_iff_circleMoments"), H("All moments characterize weak continuity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Compactness and existing measure uniqueness make the complete moment profile a topological embedding. Finite-mode reconstruction is not asserted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tendsto-iff-circlemoments"),
                DeclarationHandle.Create(Prefix + "tendsto_iff_circleMoments"), H("All moments characterize weak convergence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original complete moment profile identifies weak convergence along arbitrary filters, reusing the same compact embedding."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-moment-witnesses-tendsto"),
                DeclarationHandle.Create(Prefix + "finite_moment_witnesses_tendsto"), H("Every finite-order witness sequence has the same weak limit"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any probability witnesses matching all modes up to their respective orders converge as a whole sequence. No compatibility of consecutive choices is assumed; no quantitative rate is asserted."))), DescribeRole.Theorem))));
}
