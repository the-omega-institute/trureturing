using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves;
internal sealed class A6GaloisCosetDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6GaloisCoset." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The current compiler statement below supplies the exact telescope, hypotheses and conclusion. The full domain and original boundaries in this document apply."))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full Galois-difference fiber and translated rational group", H("Full Galois-difference fiber and translated rational group"),
        Blocks(
            Paragraph(Text("On the actual elliptic group E0(Q(sqrt43645)), fixed points of conjugation are exactly the embedded rational group. The entire fiber P-sigma(P)=T is Pstar+E0(Q). Every positive rational quartic point, with both W signs, satisfies the exact polynomial translation P=Pstar-R and has this Galois difference. Integrality is imposed on P, not on R. This module supplies the full Galois fiber. A6DyadicInfiniteOrder proves infinite order of T, full nonzero-multiple nonrationality and the received rank lower bounds. A6FullTorsion proves the full rational/quadratic torsion conclusions. A6RationalCurveIsogeny proves the full-coset obstruction in its field-universal rational coordinate-atlas representation. Exact ranks, full bases, saturation and a separate intrinsic scheme-isogeny API equivalence theorem are not claimed.")),
            Paragraph(Text("Source: original Nikandish problem; Ma/Nikandish/Zhang supplied manuscripts at PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02. Exact source blob and attribution are retained in Lean. All O1-O9, L1-L21/F1-F17, C1-C16 outcomes and original rights/publication boundaries remain binding. Exact n7 and its pause, generalQ3, a6 certification and finite-enumeration reproduction limits are unchanged. Unfinished faithful escape registration is disclosed in issue#28398; disclosure is not audit completion.")),
            Item("sigma-embed", "sigma_embed", "sigma embed"),
            Item("fixed-iff-rational", "fixed_iff_rational", "fixed iff rational"),
            Item("pstar-difference", "Pstar_difference", "Pstar difference"),
            Item("full-rational-coset", "full_rational_coset", "full rational coset"),
            Item("polynomial-translation", "polynomial_translation", "polynomial translation"),
            Item("polynomial-galois-difference", "polynomial_galois_difference", "polynomial galois difference")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6EllipticModels"))]));
}
