using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves;
internal sealed class A6TorsionDyadicAlgebraDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, bool definition) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6TorsionDyadicAlgebra." + name),
            H(name), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text("Exact original curve coefficients, full original point-group domains and prerequisite statements are read from the compiler. Ma/Nikandish/Zhang attribution is retained. The dyadic alternative and its group-coordinate engineering are task-local proof representation."))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A6TorsionDyadicAlgebra", H("Full original elliptic torsion"),
        Blocks(
            Paragraph(Text("Exact full rational-coordinate arithmetic for the entire original short E and its43645 twist. Negative horizontal valuations duplicate downward by2; unit horizontals duplicate to the negative region; every even horizontal, including0, triples to a nonzero value of nonpositive valuation. The complete scaled three-division quartic has no rational root, proved by monicity and full modulo11 certificates. These are arithmetic inputs consumed by the actual full elliptic group proof, not a finite point list or a torsion-free hypothesis.")),
            Paragraph(Text("Complete original S.torsion, blob2bb42a5280cb3ea4ebe596259d4ffbbb1fd37588 at PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02, Ma/Nikandish/Zhang. Original finite reduction groups and prime-to-p reduction argument remain source evidence; the alternative proof does not claim to have formalized that separate reduction-injectivity method. No exact rank, full basis or saturation is claimed. Full O1-O9, L1-L21/F1-F17 and C1-C16, exact n7/pause, generalQ3, a6 certification, finite-enumeration reproduction and attribution/rights boundaries remain unchanged.")),
            Item("cubic", "cubic", true),
            Item("numerator", "numerator", true),
            Item("psi3", "psi3", true),
            Item("quartic4", "quartic4", true),
            Item("doublex", "doubleX", true),
            Item("triplex", "tripleX", true),
            Item("mod11-psi3-e", "mod11_psi3_E", false),
            Item("mod11-psi3-twist", "mod11_psi3_twist", false),
            Item("e-psi3-no-root", "E_psi3_no_root", false),
            Item("twist-psi3-no-root", "twist_psi3_no_root", false),
            Item("double-negative", "double_negative", false),
            Item("double-unit", "double_unit", false),
            Item("even-triple-nonpositive", "even_triple_nonpositive", false)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6QuadraticDescent"))]));
}
