using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves;
internal sealed class A6FullTorsionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, bool definition) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6FullTorsion." + name),
            H(name), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("Exact original curve coefficients, full original point-group domains and prerequisite statements are read from the compiler. Ma/Nikandish/Zhang attribution is retained. The dyadic alternative and its group-coordinate engineering are task-local proof representation."))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A6FullTorsion", H("Full original elliptic torsion"),
        Blocks(
            Paragraph(Text("Every finite-order point of the full actual E(Q), Ed(Q), E0(Q), E0(K) and E(K) groups is the identity. The proof handles infinity and every finite point, excludes nonidentity2-torsion and3-division exceptions, proves actual duplication and triplication coordinates, and forces any putative nonzero torsion point into the region of dyadic infinite order on E0(K). The actual injective trace/twist descent supplies the full quadratic-field conclusion. No good-reduction injection, Nagell-Lutz oracle, point-list oracle, rank assumption or new axiom is used.")),
            Paragraph(Text("Complete original S.torsion, blob2bb42a5280cb3ea4ebe596259d4ffbbb1fd37588 at PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02, Ma/Nikandish/Zhang. Original finite reduction groups and prime-to-p reduction argument remain source evidence; the alternative proof does not claim to have formalized that separate reduction-injectivity method. No exact rank, full basis or saturation is claimed. Full O1-O9, L1-L21/F1-F17 and C1-C16, exact n7/pause, generalQ3, a6 certification, finite-enumeration reproduction and attribution/rights boundaries remain unchanged.")),
            Item("e-torsion-trivial", "E_torsion_trivial", false),
            Item("twist-torsion-trivial", "twist_torsion_trivial", false),
            Item("e0q-torsion-trivial", "E0Q_torsion_trivial", false),
            Item("e0k-torsion-trivial", "E0K_torsion_trivial", false),
            Item("ek-torsion-trivial", "EK_torsion_trivial", false)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6TorsionDyadicAlgebra"))]));
}
