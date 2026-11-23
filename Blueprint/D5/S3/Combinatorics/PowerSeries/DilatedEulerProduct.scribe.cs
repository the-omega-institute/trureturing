using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PowerSeries;

internal sealed class DilatedEulerProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/yaqubi2026designatedsummands");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Euler products at multiples of a positive degree.",
        H("Dilated Euler products"),
        Blocks(
            Paragraph(Text("A dilated Euler series has constant coefficient one, so it defines a unit. Its finite products converge coefficientwise over discrete coefficient rings. Changing the coefficient ring preserves the unit because the undilated coefficients are signed pentagonal indicators.")),
            Node("euler", "Dilate the pentagonal series by a positive natural degree.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("etaUnit", "The corresponding unit, with inverse at constant coefficient one.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("tendsto_expand_discrete", "Dilation is continuous for coefficientwise convergence over a discrete ring.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("euler_tendsto", "The finite Euler products with exponents d(i+1) converge to the dilated series.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("euler_const", "The constant coefficient of a dilated Euler product is one.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("map_eta", "A ring homomorphism on the coefficients preserves the dilated Euler unit.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("expand_eta", "Dilating an Euler unit again multiplies its dilation index.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("prod_split_two", "A product through 2N consecutive indices is the product through the N even and the N odd indices.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string declaration, string narrative, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("dilatedeulerproduct-" + declaration.ToLowerInvariant().Replace('_', '-').Replace('₀', '0')),
            DeclarationHandle.Create(Prefix + declaration), H(declaration),
            StatementSource.WithoutFormula(), provenance, Blocks(Paragraph(Text(narrative))), role);
}
