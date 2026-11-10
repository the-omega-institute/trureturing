using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves;
internal sealed class RootTwoAffineGeometryDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, bool definition) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/RootTwoAffineGeometry." + name),
            H(name), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The exact original quartic, entire rational a>=2 domain, arbitrary extension fields and full affine coordinate algebra are compiler-read. Ma/Nikandish/Zhang retain original source attribution. The fraction-field descent, tensor presentation and actual Spec transport are task-local proof representation."))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "RootTwoAffineGeometry", H("Geometric integrality of the full original affine curve"),
        Blocks(
            Paragraph(Text("For every rational a>=2 the actual affine curve with the entire original quartic equation is geometrically integral over Q. Separability after every extension excludes squares in the fraction field, Gauss descent proves the actual quadratic polynomial irreducible, and the tensor algebra equivalence identifies every field base change with the same full equation. The theorem concerns the actual Spec structure morphism, not a disconnected family of proxy rings. The original rational zero-tail point supplies a full-coordinate-algebra point in the transient native application evidence; it is not asserted to be a positive graph exponent.")),
            Paragraph(Text("Complete original S.root2curve, blobf3751b6be960a3712fd9c7a7a532c06bfc39e80f, SHA2562ac5c5e1ad23693e4f1ea750a5303d9ba15e2d6613e0ff133471ad9e133eb064, at PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02, Ma/Nikandish/Zhang. Smooth projective normalization, genus one and the original Siegel method remain separate unfinished obligations. Existing full fixed-a positive-integral finiteness has a direct proof and does not establish those missing method claims. No original old E/H allowance is renewed; fullE3 and unknown old balances remain exact gaps. Exact n7/pause, generalQ3, a6 certification, finite enumeration limits, original failed methods, reports, uncertainty and attribution remain unchanged. Issue28398 uses the precise unfinished-audit disclosure route, not completed escape validation or a waiver.")),
            Item("plane-polynomial", "planePolynomial", true),
            Item("plane-polynomial-irreducible", "planePolynomial_irreducible", false),
            Item("coordinate-ring", "CoordinateRing", true),
            Item("coordinate-ring-domain", "coordinateRing_isDomain", false),
            Item("affine-curve", "affineCurve", true),
            Item("base-change-equivalence", "baseChangeEquiv", true),
            Item("structure-morphism", "structureMorphism", true),
            Item("geometrically-integral", "affineCurve_geometricallyIntegral", false)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/RootTwoTailCurve"))]));
}
