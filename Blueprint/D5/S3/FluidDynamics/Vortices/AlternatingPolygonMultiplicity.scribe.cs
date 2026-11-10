using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Vortices;

internal sealed class AlternatingPolygonMultiplicityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FluidDynamics/barrykevrekidis2013vortex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Algebraic multiplicity is computed as polynomial root multiplicity over the complex numbers. Each nonzero matching mode contributes one. The folded fibre count gives multiplicity one at the endpoints and two internally. Collision exclusion consumes the existing positive-root separation proof and separates the nonpositive squared modes. Zero has algebraic multiplicity two for every m at least one.",
        H("Alternating Polygon Multiplicity"), Blocks(
            Paragraph(Text("The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.")),
            Node("squaredValue", "squaredValue", "The squared spectral value of a folded label.", DescribeRole.Definition),
            Node("squaredValue_injective", "squaredValue injective", "There are no collisions between different folded squared modes. The positive-positive case consumes the canonical integer separation proof.", DescribeRole.Theorem),
            Node("nonzero_algebraic_multiplicity", "nonzero algebraic multiplicity", "A nonzero root has exactly one eigenline in each matching Fourier block; this computes its full algebraic multiplicity, including repeated labels.", DescribeRole.Theorem),
            Node("algebraic_multiplicity_of_mode", "algebraic multiplicity of mode", "Exact nonzero algebraic multiplicity at a folded squared mode.", DescribeRole.Theorem),
            Node("zero_algebraic_multiplicity", "zero algebraic multiplicity", "The zero root has algebraic multiplicity exactly two, including dipole and square.", DescribeRole.Theorem),
            Node("complex_root_iff_mode", "complex root iff mode", "Root classification in the complete complex field, before choosing square roots.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("alternating-polygon-multiplicity-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
