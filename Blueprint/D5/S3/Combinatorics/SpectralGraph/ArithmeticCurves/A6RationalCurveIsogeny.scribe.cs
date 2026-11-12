using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves;
internal sealed class A6RationalCurveIsogenyDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, bool definition) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6RationalCurveIsogeny." + name),
            H(name), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The compiler statement specifies every actual source and target elliptic point group and all fields. The finite rational homogeneous coordinate atlas is the proof representation; original scientific credit is retained, and this representation and polynomial-equivariance engineering are task-local."))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational curve morphisms and the full Galois obstruction", H("Rational curve morphisms and the full Galois obstruction"),
        Blocks(
            Paragraph(Text("An actual rational curve map is represented on a finite Zariski cover by homogeneous polynomial triples over Q, with a full elliptic point-group realization over every characteristic-zero field. The cover and regularity data cover every point, including infinity. Finite kernel is required on those full groups. Galois compatibility is derived from the rational polynomial charts; it is not assumed for an arbitrary finite-kernel group homomorphism. Every point in the entire received Galois-difference coset has a nonrational image under every map in this representation, for every actual Weierstrass target over Q.")),
            Paragraph(Text("Original complete S.nontorsion, blob01edb67a7e6753c17ecae77e581d4957fe6b94cc at PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02, Ma/Nikandish/Zhang. The precise formal domain is the field-universal finite rational coordinate-atlas representation. No separate equivalence theorem with an intrinsic scheme-isogeny API is claimed. A6FullTorsion proves the full rational/quadratic torsion conclusions by an alternative dyadic argument. The original good-reduction injection method remains unformalized. Full O1-O9, L1-L21/F1-F17 and C1-C16, exact n7/pause, generalQ3, a6 certification, finite enumeration reproduction and all original source/rights boundaries remain binding. Issue28398 is unfinished faithful escape-registration disclosure, not proof, audit completion or a waiver.")),
            Item("coordinates", "coordinates", true),
            Item("rationalcurveisogeny", "RationalCurveIsogeny", true),
            Item("targetsigma", "targetSigma", true),
            Item("targetembed", "targetEmbed", true),
            Item("isogeny-sigma", "isogeny_sigma", false),
            Item("isogeny-t-infinite-order", "isogeny_T_infinite_order", false),
            Item("isogeny-no-rational-image", "isogeny_no_rational_image", false)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6DyadicInfiniteOrder"))]));
}
