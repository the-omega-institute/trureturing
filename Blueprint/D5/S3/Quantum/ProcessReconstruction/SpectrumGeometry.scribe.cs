using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class SpectrumGeometryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/SpectrumGeometry";

    private static readonly LibraryNoteRef Bravyi = LibraryNoteRef.Create("D5/L/ProcessReconstruction/bravyi2026identitycheck");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Angular estimates for chains of unit vectors and chord bounds for finite unit-circle sets.",
        H("Unit-Circle Diameter Geometry"),
        Blocks(
            Describe.Lean(DescribeId.Create("diameter-half-plane"),
                DeclarationHandle.Create(Module + ".circle_diameter_halfPlane"),
                H("A common supporting line from a diameter pair"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Bravyi),
                Blocks(Paragraph(Text(
                    "Take two unit complex numbers p and q with distance less than √3. There is "
                    + "a common unit phase and a positive real threshold t with t squared equal to "
                    + "one minus one quarter of the squared chord length. Every unit point within "
                    + "that chord length of both endpoints has real part at least t after the same "
                    + "rotation. For a spectrum, the two distance hypotheses follow by taking a "
                    + "pair that attains its diameter."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("short-spherical-chain"),
                DeclarationHandle.Create(Module + ".finset_unit_chord_lt_sqrt_three"),
                H("Endpoint chord for a chain with small increments"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Bravyi),
                Blocks(Paragraph(Text(
                    "Consider an insertion chain of unit vectors. When the chord of each step "
                    + "has an upper bound at most one, the angle of that step is at most π/3 "
                    + "times its chord bound. A total of those bounds strictly below two "
                    + "forces the endpoint chord to be shorter than √3."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("positive-spectral-hull"),
                DeclarationHandle.Create(Module + ".unitCircle_halfPlane_with_chord_of_zero_not_mem_convexHull"),
                H("A supporting line at the nearest point of the convex hull"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Bravyi),
                Blocks(Paragraph(Text(
                    "For a nonempty finite set on the unit circle whose convex hull excludes "
                    + "zero, the nearest point of the hull to zero gives a positive supporting "
                    + "threshold t after a common rotation. The set contains two points with "
                    + "chord length 2√(1−t²), with coincident endpoints permitted when t is one."))),
                DescribeRole.Lemma))));
}
