using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class PlanarWilsonLoopAreaLawDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/PlanarWilsonLoopAreaLaw.";
    private static LibraryNoteRef Ising => LibraryNoteRef.Create("D5/L/SpinModels/wegner2014generalizedising");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact Wilson-loop area law in the two-element gauge theory on an open planar box.",
        H("Exact planar Wilson-loop area law"),
        Blocks(
            Paragraph(Text(
                "The incidence matrix records the four geometric edges of each unit plaquette over Z/2Z. "
                + "The Wilson expectation is the sum over bit link configurations of the parity character "
                + "of the inserted edge chain times the Boltzmann weight, divided by the sum of the weights.")),
            Paragraph(Text(
                "For every real β and s equal to 1 or −1, exp(βs) = cosh(β)(1 + s tanh(β)). "
                + "The frozen high-temperature expansion eliminates all surfaces except those with the "
                + "prescribed mod-two boundary, yielding the ratio of the inserted and closed surface sums. "
                + "The common factor cosh(β) raised to the number of plaquettes times two raised to the "
                + "number of links is nonzero for every real β.")),
            Paragraph(Text(
                "In an open planar box, pairing the boundary with a ray isolates each plaquette coefficient. "
                + "The mod-two boundary is therefore injective. The rectangle filling has exactly width times "
                + "height plaquettes, and adjacent edges cancel in pairs, giving the four side sums. "
                + "When either side length is zero the coincident side chains cancel and the filling is empty.")),
            Describe.Lean(DescribeId.Create("wilson-loop-2d"),
                DeclarationHandle.Create(Prefix + "wilson_loop_2d_exact_area_law"),
                H("Exact Wilson-loop area law in two dimensions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Ising),
                Blocks(Paragraph(Text(
                    "For arbitrary natural side lengths of the containing open box and any axis-aligned "
                    + "rectangle that fits inside it, including zero width or height, the perimeter has a "
                    + "unique bit plaquette filling. For every real β the normalized expectation equals "
                    + "tanh(β)^(width × height). For β > 0 the string tension σ = −log(tanh(β)) is positive "
                    + "and the same expectation equals exp(−σ × (width × height)). "
                    + "The proof applies the repository's frozen parity expansion to the rectangle boundary. "
                    + "Wegner's cited expansion supplies the literature background for the closed-surface sum."))),
                DescribeRole.Theorem))));

}
