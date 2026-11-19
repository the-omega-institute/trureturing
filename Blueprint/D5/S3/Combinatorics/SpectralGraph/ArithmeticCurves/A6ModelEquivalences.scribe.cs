using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves;
internal sealed class A6ModelEquivalencesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, bool definition) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6ModelEquivalences." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The compiler statement supplies the exact actual point groups and complete domain. Generic affine scaling and point-group engineering are task-local; original scientific conclusions retain the source attribution above."))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual elliptic model group isomorphisms and twist rank", H("Actual elliptic model group isomorphisms and twist rank"),
        Blocks(
            Paragraph(Text("Full actual point-group isomorphisms connect E0(Q) with E(Q), E0(K) with E(K), and E(K) with Ed(K), using exact affine scaling, addition and bijectivity proofs. The original rational S and Galois-difference T map to their exact received short-model and twist coordinates. The actual rational twist witness has infinite order. The received rank lower bounds are1 over Q for E/E0/Ed and2 over K for E/E0; no exact rank, basis or saturation is asserted. S is a group control: its original c=26065/271 is not an integer graph example. A6FullTorsion now supplies the full rational/quadratic torsion conclusions by a dyadic proof. A6RationalCurveIsogeny supplies the full-coset obstruction in the field-universal rational coordinate-atlas representation, without a separate intrinsic scheme-API equivalence theorem. Finite reduction counts and two-torsion exclusion alone do not supply the separately unformalized good-reduction torsion-injection method.")),
            Paragraph(Text("Original Nikandish problem and Ma/Nikandish/Zhang manuscripts at PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02, complete S.nontorsion and S.torsion source blobs attributed in Lean. The exact native localization application supplies an injective embedding of the actual Localization.Away(10:O_K) into K, and places every integral long-model coordinate pair in that localization after short-model scaling, including both signs of every integer quartic pair and all half-integer fibers. Full O1-O9, L1-L21/F1-F17 and C1-C16 remain binding, with exact n7/pause, generalQ3, a6 certification, finite enumeration reproduction and original attribution/rights boundaries unchanged.")),
            Item("shortqequiv", "shortQEquiv", "shortQEquiv", true),
            Item("shortkequiv", "shortKEquiv", "shortKEquiv", true),
            Item("twistkequiv", "twistKEquiv", "twistKEquiv", true),
            Item("short-s-infinite-order", "short_S_infinite_order", "short S infinite order", false),
            Item("short-rational-rank-lower", "short_rational_rank_lower", "short rational rank lower", false),
            Item("short-quadratic-rank-lower", "short_quadratic_rank_lower", "short quadratic rank lower", false),
            Item("short-s-image", "short_S_image", "short S image", false),
            Item("twist-t-image", "twist_T_image", "twist T image", false),
            Item("twistwitness-infinite-order", "twistWitness_infinite_order", "twistWitness infinite order", false),
            Item("twist-rational-rank-lower", "twist_rational_rank_lower", "twist rational rank lower", false),
            Item("shortk-some", "shortK_some", "All short-model finite coordinates", false),
            Item("twistk-some", "twistK_some", "All twist finite coordinates", false)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6DyadicInfiniteOrder")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6TorsionArithmetic"))]));
}
