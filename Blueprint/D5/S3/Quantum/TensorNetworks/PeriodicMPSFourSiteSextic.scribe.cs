using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFourSiteSexticDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four-site periodic matrix product state sextic and its first-order boundary vanishing",
        H("The four-site periodic sextic"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodic-four-site-sextic"),
                DeclarationHandle.Create(Module + ".sextic"), H("The necklace polynomial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The six inputs are the amplitudes of 0000, 1000, 1100, 1010, 1110 and 1111. The polynomial is written in powers of the singlet coordinate d minus c."))),
                DescribeRole.Definition),
            Theorem("sextic_actual", "Vanishing on the actual tensor image",
                "The two-by-two trace recurrence writes the six amplitudes in terms of two traces, two determinants and one mixed trace. Substitution into the Critch–Morton sextic gives zero for every pair of complex bond matrices."),
            Theorem("sextic_rank_one_triplet", "First-order vanishing at the rank-one triplet boundary",
                "On the triplet rank-one parametrization, the sextic vanishes for arbitrary first-order variations in the six coordinates."),
            Theorem("sextic_singular_triplet_zero_singlet", "First-order vanishing at the zero-singlet boundary",
                "When the singlet vanishes and the triplet is singular, the sextic has zero value and zero first derivative. The negative square and triplet determinant formula yields both vanishings."),
            Theorem("phase_of_proportional_flattening", "Equal nonzero marginal fixes the norm of the phase",
                "For proportional four-site flattenings with a common nonzero raw two-site marginal, the proportionality scalar has absolute value one and relates every full amplitude."))));

    private static DocumentBlock Theorem(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodic-four-site-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
