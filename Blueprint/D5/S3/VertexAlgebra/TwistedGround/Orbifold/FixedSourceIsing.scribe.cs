using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Orbifold;

internal sealed class FixedSourceIsingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-source Ising modes on the odd twisted sector",
        H("Fixed-source Ising modes on the odd twisted sector"),
        Blocks(
            Paragraph(Text("Given hu : IsUnit D.G.det, the actual odd twisted sector is "
                + "paritySpace D hu (-1).")),
            Entry("odd-iterate", "odd_iterate", "Fixed-source iterate",
                "The Borcherds law for two fixed sources gives the iterate on the actual odd twisted sector. "
                + "The source of the iterated coefficient is formed with the fixed lattice mode."),
            Entry("odd-commutator", "odd_commutator", "Fixed-source commutator",
                "The same law expresses the commutator on the odd sector as a binomially weighted sum "
                + "of modes of fixed lattice products."),
            Entry("odd-axis-mode", "oddAxisMode", "Actual odd axis mode",
                "The Virasoro mode L(m) is coefficient m + 1 of the fixed norm-four source on the negative parity slice.",
                DescribeRole.Definition),
            Entry("odd-virasoro", "odd_virasoro", "Virasoro action at central charge one half",
                "For norm four and a parameter s with s² = 1, the axis self-products truncate the commutator "
                + "to four terms. Translation gives the derivative term and the odd vacuum coefficient "
                + "gives (m³ − m)/24 when m + n = 0."),
            Entry("fixed-virasoro", "fixed_virasoro", "Virasoro action on the fixed lattice subspace",
                "The lattice Virasoro relation at central charge one half restricts to the fixed subspace "
                + "for a norm-four charge and s² = 1."),
            Entry("embedded-virasoro", "embedded_virasoro", "Virasoro action of the embedded axis",
                "Assume the real Gram matrix D.G.map (Int.cast : ℤ → ℝ) is positive definite, "
                + "⟨a, a⟩ = 4, and s² = 1. Combining the fixed lattice and actual odd relations "
                + "gives Virasoro for the literal embedded axis "
                + "on the original two-sector carrier."),
            Entry("level-six-null-source", "nullState", "Level-six vacuum descendant",
                "Form the vacuum descendant with coefficients 64, 93, −264 and −108 using the fixed lattice modes.",
                DescribeRole.Definition),
            Entry("fixed-vacuum-null", "fixed_vacuum_null", "Vanishing of the fixed vacuum descendant",
                "For a norm-four charge and s² = 1, the lattice relation makes the level-six descendant "
                + "zero in the fixed subspace."),
            Entry("odd-vacuum-null", "odd_vacuum_null", "Vanishing of every odd null coefficient",
                "For ⟨a, a⟩ = 4 and s² = 1, the level-six vacuum descendant vanishes in the fixed lattice. "
                + "Linearity in the fixed source then makes every coefficient of this descendant "
                + "vanish on the odd twisted sector."))));

    private static DocumentBlock Entry(string id, string declaration, string heading, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
