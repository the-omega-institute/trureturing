using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq207EulerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq207Euler.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/andrews2025positive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Euler factors define a unique normalized coefficient series and its Laurent expansion.",
        H("Formal Euler Expansion"),
        Blocks(
            Node("inversionseq207-euler-euler-denominator", "Euler denominator", "eulerDenominator", "For a natural number index, eulerDenominator is the finite product of 1 minus the power-series variable raised to each positive exponent below index.", DescribeRole.Definition),
            Node("inversionseq207-euler-euler-coefficients", "Euler coefficient series", "eulerCoefficients", "For a natural number index, eulerCoefficients is the signed monomial at the triangular exponent multiplied by the inverse of eulerDenominator with constant coefficient one.", DescribeRole.Definition),
            Node("inversionseq207-euler-euler-laurent-expansion", "Laurent expansion", "eulerLaurentExpansion", "The Laurent expansion is the power series whose coefficient at each degree is the finite sum of Euler coefficients paired with Laurent monomials indexed by natural numbers.", DescribeRole.Definition),
            Node("inversionseq207-euler-euler-coefficient-construction", "Euler coefficient construction", "euler_coefficient_construction", "The Euler coefficient series has constant coefficient one and satisfies the rescaling equation series equals (1 minus q) times its q-rescaling. It is the unique series with these properties. Its coefficients vanish below the triangular support, admit the finite polynomial coefficient description, and sum as a Laurent power series to eulerLaurentExpansion.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
