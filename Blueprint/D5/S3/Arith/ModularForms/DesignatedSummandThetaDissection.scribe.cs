using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class DesignatedSummandThetaDissectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/yaqubi2026designatedsummands");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A parity bijection dissects the complete product U(q)U(q³).",
        H("The Jacobi parity dissection"),
        Blocks(
            Paragraph(Text("The three factors use the weighted Jacobi specialization, a sign twist on the Laurent support cone, and constant-unit evaluation. For the product U(q)U(q³), write the starting integer indices as a and b. The two affine coordinates come from a+3b and a−b divided by two. Folding one coordinate in each parity case gives the two disjoint lattices. The bijection preserves the degrees and turns the original signs into a positive even summand and a negative odd summand. The contributing index pairs at each fixed degree lie in a finite set.")),
            Node("U", "The signed weighted Jacobi sum at weight parameters 2 and 1.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("phi", "The bilateral theta series with square exponents.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("psi", "The unilateral theta series with triangular exponents.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("U_product", "The series U times the Euler factor f2 is f4 f1.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("phi_product", "The series phi times f1 squared and f4 squared is f2 to the fifth power.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("psi_product", "The series psi times f1 is f2 squared.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("U_dissection", "Over the rationals, U(q) U(q³) equals psi(q⁴) phi(q⁶) minus q phi(q²) psi(q¹²).", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string declaration, string narrative, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("designatedsummandthetadissection-" + declaration.ToLowerInvariant().Replace('_', '-').Replace('₀', '0')),
            DeclarationHandle.Create(Prefix + declaration), H(declaration),
            StatementSource.WithoutFormula(), provenance, Blocks(Paragraph(Text(narrative))), role);
}
