using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class SlaterSpectatorMinorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/SlaterSpectatorMinor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered Slater minors with an appended orbital",
        H("Ordered Slater minors with an appended orbital"),
        Blocks(
            Entry("appendOrbital", "Appending a coordinate orbital",
                "For a complex site-by-orbital matrix V and a site p in the linearly ordered site type, append a last column with entry one at p and zero elsewhere. The other columns retain their order and entries.",
                DescribeRole.Definition),
            Entry("occupiedMinor", "The minor on an occupied set",
                "Given a finite set S of sites and a complex site-by-orbital matrix with k columns, take the determinant of the rows of S in increasing site order when S has size k. For every other size the value is zero.",
                DescribeRole.Definition),
            Entry("occupiedMinor_append", "The cofactor of the appended coordinate",
                "For every finite occupied set S, the minor for the appended matrix vanishes when p is absent from S. When p is present, it equals the original occupied minor on S with p removed, times minus one to the power of the number of elements of S strictly greater than p. The removal preserves the increasing enumeration of the other rows. The cofactor position in the last column has this parity for every occupied set of the matching size, and the zero convention gives the formula for all other sizes.",
                DescribeRole.Theorem),
            Entry("canonical_ordered_spectator_extension", "The unique ordered extension by coordinate orbitals",
                "For an orthonormal orbital matrix on a finite ordered site type and a finite set T of zero rows, there is exactly one extension with the original k columns in order followed by the coordinate columns for T in increasing order. The matrix has k plus the cardinality of T columns. These columns are orthonormal and every original zero row outside T remains zero. For any finite occupied set S, the extended minor vanishes unless S contains all of T. When S contains T, the extended minor is the original minor on S with T removed, multiplied by minus one to the power of the number of pairs consisting of a site in T and a later site in S outside T. Removing the largest appended site iterates the one-coordinate cofactor and keeps the order of the other spectator rows.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("slater-spectator-minor-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
