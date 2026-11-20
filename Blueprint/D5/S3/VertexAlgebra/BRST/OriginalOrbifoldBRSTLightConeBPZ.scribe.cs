using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.BRST;

internal sealed class OriginalOrbifoldBRSTLightConeBPZDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTLightConeBPZ";

    private static DocumentBlock Node(
        string name, string heading, DescribeRole role, string statement) =>
        Describe.Lean(
            DescribeId.Create("original-orbifold-brst-light-cone-bpz-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Light-cone degree selection for native relative BPZ",
        H("Light-cone degree selection for native relative BPZ"),
        Blocks(
            Node("integerWick_frame_degree", "Oscillator degree selection", DescribeRole.Theorem,
                "The native integer Wick form of two null-frame monomials vanishes if their signed oscillator degrees sum to a nonzero integer. The normalized frame occupies the two original coordinate lines in either order. Retuning preserves their signed weights, and the hyperbolic Gram substitution reverses them at each frequency."),
            Node("Homogeneous", "Light-cone homogeneity", DescribeRole.Definition,
                "A state is homogeneous in a fixed frame and degree if all nonzero coefficients in its native null-frame tensor basis have that degree. The degree of a basis label adds the signed oscillator degree and the ghost charge, then subtracts one."),
            Node("shellBPZ_degree_selection", "Relative mass-shell selection", DescribeRole.Theorem,
                "The native relative BPZ pairing between homogeneous states of opposite momenta vanishes if their light-cone degrees sum to a nonzero integer. Both states use the same normalized frame. The relative ghost pairing forces the two ghost charges to sum to two, so their shifted degrees cancel."),
            Node("beta_ground_ghost", "Relative ground ghost scalar", DescribeRole.Theorem,
                "For the actual ghost ket with occupied set {1}, the BPZ form with the zero mode of c inserted on the right is −1. The relative ghost bilinear coefficient is +1 and the BPZ phase on the first ket is −1."),
            Node("shellBPZ_inclusion", "Pairing of quartet ground inclusions", DescribeRole.Theorem,
                "When the two ground inclusions are defined on opposite relative mass shells, their native pairing is the negative of the orbifold pairing of the two included states. The lattice ground factor has Wick coefficient one. The literal lattice reflection reverses momentum and fixes the oscillator unit."))));
}
