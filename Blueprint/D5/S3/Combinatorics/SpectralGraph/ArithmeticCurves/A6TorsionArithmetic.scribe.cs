using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves;
internal sealed class A6TorsionArithmeticDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, bool taskLocal) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6TorsionArithmetic." + name),
            H(title), StatementSource.WithoutFormula(), taskLocal ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The current compiler statement supplies the exact full telescope. Attribution and remaining boundaries above apply."))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite elliptic reduction groups and rational two-torsion exclusion", H("Actual finite elliptic reduction groups and rational two-torsion exclusion"),
        Blocks(
            Paragraph(Text("The full actual nonsingular point groups, including infinity, have orders10 and16 for E mod11 and17, and14 and20 for its43645 twist. The complete mod23 domain proves the rational cubic has no root, and the actual E(Q) and Ed(Q) groups have no nonidentity two-torsion. These counts alone do not prove the full received torsion theorem. A6FullTorsion proves all received rational and quadratic torsion-triviality conclusions by an alternative dyadic argument. Full prime-to-p good-reduction torsion injectivity remains a separately unformalized source method.")),
            Paragraph(Text("Original Nikandish problem and Ma/Nikandish/Zhang supplied manuscripts at PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02. Exact original blobs are attributed in Lean. Full O1-O9, L1-L21/F1-F17, C1-C16, n7 and paused exclusions, generalQ3, a6 certification, finite-enumeration reproduction limits and rights/publication boundaries remain unchanged.")),
            Item("integere-rational", "integerE_rational", "integerE rational", false),
            Item("reductione11", "reductionE11", "reductionE11", false),
            Item("reductione17", "reductionE17", "reductionE17", false),
            Item("reductiontwist11", "reductionTwist11", "reductionTwist11", false),
            Item("reductiontwist17", "reductionTwist17", "reductionTwist17", false),
            Item("e11-order", "E11_order", "E11 order", false),
            Item("e17-order", "E17_order", "E17 order", false),
            Item("twist11-order", "twist11_order", "twist11 order", false),
            Item("twist17-order", "twist17_order", "twist17 order", false),
            Item("mod23-no-root", "mod23_no_root", "mod23 no root", false),
            Item("rational-no-root", "rational_no_root", "rational no root", false),
            Item("twist-no-root", "twist_no_root", "twist no root", false),
            Item("e-no-two-torsion", "E_no_two_torsion", "E no two torsion", false),
            Item("twist-no-two-torsion", "twist_no_two_torsion", "twist no two torsion", false)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6EllipticModels"))]));
}
