using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class TwoUnitExponentSpectrumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both explicit irrational eigenvalues on every two-unit-exponent ideal graph.",
        H("The full two-unit-exponent spectral family"),
        Blocks(
            Paragraph(Text("Source: PR3 b93becea662a746badeadba42fdc3d3eb3db9382, paper/sections/pqrk.tex, blob7c91c849ebd0b16c81fd5344f4a210bd077db5b1. Original Nikandish graph/problem attribution and manuscript Ma/Nikandish/Zhang credit, prerequisites, failed methods, reports, uncertainties and rights boundaries are preserved. The stronger already delivered unit-exponent nonintegrality result is reused at its original scope. This module preserves the additional explicit full spectral result, with every positive third exponent and arbitrary distinct primes. The coordinate type is the disjoint union of two paired coordinates and one remaining coordinate; arbitrary prime assignment retains every prime-coordinate permutation. No bound or ordering on the primes is imposed.")),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/TwoUnitExponentSpectrum.result"),
                H("Both irrational eigenvalues for every positive third exponent"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every positive integer k, both signs in (6k+1 plus or minus sqrt((2k+2)^2-3))/2 are irrational and are eigenvalues of the actual nonzero-proper-ideal intersection graph with exponent vector (1,1,k). The complete two-dimensional K restriction intertwines with the full subset operator; a nonzero residual vector lifts to a nonzero actual ideal-graph vector. Strict adjacent-square bounds prove irrationality. Neither an assumed eigenpair nor a scalar proxy replaces the original graph statement. Exact n7 and its paused exclusions, general Q3, a6 certification, finite-enumeration reproduction limits and full E3 remain separate boundaries. The escape audit at issue28398 is unfinished: source realization/readout, sourceSelection, full-family intervention, observation-dependence, sensitivity and current binding evidence are not supplied by this disclosure."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairSupport"))]));
}
