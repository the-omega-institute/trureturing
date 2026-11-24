using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Characters;

internal sealed class ActualLeechMixedVerlindeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite character calculation and the native Leech mixed field spaces have matching multiplicities.",
        H("Actual Leech Mixed Verlinde Comparison"),
        Blocks(
            Entry("verlinde-coefficient", "verlindeCoefficient", "Finite Verlinde coefficient",
                "The coefficient is the normalized triple product sum using the matrix acting on the four literal sector characters.",
                DescribeRole.Definition),
            Entry("twisted-label", "twistedLabel", "Twisted sector label",
                "Negative oscillator parity selects B and positive oscillator parity selects C.",
                DescribeRole.Definition),
            Entry("mixed-coefficient-space", "mixedCoefficientSpace", "Native mixed coefficient line",
                "The line is the span of the native mixed field's coefficients in the space of coefficient families.",
                DescribeRole.Definition),
            Entry("mem-mixed-coefficient-space", "mem_mixedCoefficientSpace", "Lawful coefficient families",
                "The actual multiplicity-one theorem identifies the line with all coefficient families satisfying the lower truncation, translation and signed Jacobi laws of a lawful mixed field.",
                DescribeRole.Theorem),
            Entry("mixed-coefficient-space-finrank", "mixedCoefficientSpace_finrank", "Native field dimension",
                "The native field has a nonzero coefficient in each direction, so each coefficient space has complex dimension one.",
                DescribeRole.Theorem),
            Entry("mixed-verlinde-agreement", "mixed_verlinde_agrees_with_native_finrank", "Mixed multiplicity comparison",
                "Multiplication by the anti-fixed lattice label selects C from B and B from C in the finite coefficient sum. The selected entry equals the dimension of the corresponding lawful field space, and the other entries in each row vanish.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
