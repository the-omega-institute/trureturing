using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCoordinates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace coordinates for five-site periodic binary bond-two states",
        H("Trace coordinates for five-site periodic binary bond-two states"),
        Blocks(
            Claim("trace_word_necklaces", "Homogeneous necklace amplitudes",
                "The eight cyclic amplitudes are weighted degree-five polynomials in the two traces, two determinants and mixed trace."),
            Claim("flatten_gram", "The physical Gram matrix",
                "Cyclicity identifies the actual adjacent two-site marginal with the Hermitian Gram matrix of the necklace flattening."),
            Claim("exists_trace_coordinates", "Realization of every trace tuple",
                "A companion matrix and an upper triangular matrix realize the invariants using one complex quadratic root."),
            Claim("aligned_inverse", "Reconstruction on the trace-aligned chart",
                "After division by the trace factor, three amplitude ratios recover the three projective source ratios."))));

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodicmpsfivesitecoordinates-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
