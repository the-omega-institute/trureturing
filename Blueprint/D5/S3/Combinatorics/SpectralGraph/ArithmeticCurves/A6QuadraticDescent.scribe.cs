using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves;
internal sealed class A6QuadraticDescentDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, bool definition) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6QuadraticDescent." + name),
            H(name), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The compiler statement gives the full actual elliptic point groups and complete parameter domain. Choice of a unique rational preimage uses the proved injective field maps. Original scientific attribution is retained; quadratic-algebra and group-descent engineering is task-local."))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full quadratic elliptic group descent", H("Full quadratic elliptic group descent"),
        Blocks(
            Paragraph(Text("Every point of the full actual E0(K) group has a rational trace and a rational twist component. Their product is an injective homomorphism into E0(Q) times Ed(Q). The full short cubic has no root in K, and the full actual E(K) and E0(K) point groups have no nonidentity two-torsion. Every anti-invariant point maps to a rational point of the actual twist, including the point at infinity. No point enumeration or assumed torsion-free group replaces these full-domain statements.")),
            Paragraph(Text("Complete original S.torsion, blob2bb42a5280cb3ea4ebe596259d4ffbbb1fd37588 at PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02, Ma/Nikandish/Zhang. This descent, finite reduction orders and no-two-torsion alone do not prove full torsion triviality. A6FullTorsion supplies the complete rational and quadratic torsion conclusions by an alternative dyadic proof; the original prime-to-p good-reduction injection method remains unformalized. A6RationalCurveIsogeny supplies the full-coset obstruction in its field-universal rational coordinate-atlas representation, without a separate intrinsic scheme-API equivalence theorem. Full O1-O9, L1-L21/F1-F17 and C1-C16, exact n7/pause, generalQ3, a6 certification, finite-enumeration reproduction and source attribution/rights boundaries remain unchanged. Issue28398 discloses unfinished faithful escape-registration evidence, not proof, audit completion or a gate waiver.")),
            Item("sigma-twice", "sigma_twice", false),
            Item("trace-rational", "trace_rational", false),
            Item("anti-sigma", "anti_sigma", false),
            Item("quadratic-no-root", "quadratic_no_root", false),
            Item("shortk-no-two-torsion", "shortK_no_two_torsion", false),
            Item("e0k-no-two-torsion", "E0K_no_two_torsion", false),
            Item("anti-to-twist-rational", "anti_to_twist_rational", false),
            Item("tracehom", "traceHom", true),
            Item("antihom", "antiHom", true),
            Item("descenthom", "descentHom", true),
            Item("descent-injective", "descent_injective", false)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6ModelEquivalences"))]));
}
