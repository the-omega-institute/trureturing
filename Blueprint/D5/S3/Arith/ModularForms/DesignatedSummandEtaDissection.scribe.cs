using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class DesignatedSummandEtaDissectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/yaqubi2026designatedsummands");
    private static readonly LibraryNoteRef Sellers = LibraryNoteRef.Create("D5/L/Fourier/sellers2023designatedsummands");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parity dissections of the designated-summand generating series and its inverse.",
        H("Integral reciprocal and square dissections"),
        Blocks(
            Paragraph(Text("The Jacobi product identities turn the parity dissection into an identity between Euler units. The coefficient map from integers to rationals is injective, so the reciprocal dissection holds integrally. Pairing odd Euler factors at q and −q gives the sign norm used to square F. The factor W reduces modulo four to f6 squared, which is supported on even degrees.")),
            Node("H", "The inverse unit of the generating series F.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("H0", "The series whose degree doubling is the even part of H.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("T", "The series whose degree quadrupling, shifted by one, gives the negative odd part of H.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("FH", "The product of F and H is one.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("H_dissection", "Over the integers, H(q) is H0(q²) minus q T(q⁴).", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Sellers)),
            Node("H_support", "The integral coefficient of H in degree 4n+3 vanishes for every natural n.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("E", "The unexpanded even part of F squared.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("W", "The integral Euler quotient f2^4 f6^4 divided by f1^8 f3^4.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("F_square", "Over the integers, F(q) squared is E(q²) plus 2q W(q²).", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("W_support", "Every odd coefficient of W is divisible by four.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string declaration, string narrative, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("designatedsummandetadissection-" + declaration.ToLowerInvariant().Replace('_', '-').Replace('₀', '0')),
            DeclarationHandle.Create(Prefix + declaration), H(declaration),
            StatementSource.WithoutFormula(), provenance, Blocks(Paragraph(Text(narrative))), role);
}
