using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons.PolygonEarSlideFormula;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;

internal sealed class PolygonEarSlideMapsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Polygons/PolygonEarSlideMaps.";
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("polygon-ear-slide-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete polygon ear slide maps",
        H("Mutually inverse maps on actual triangulations"), Blocks(
            Node("avoidTwo_of_mem_triangulation", "Ear-centre exclusion", Scope(All("T", Chords, All("e", Chord,
                Imp(Lower(6), Imp(Tri(X("T")), Imp(InF(Ear(2), X("T")), Imp(InF(X("e"), X("T")), C("AvoidTwo", X("e"))))))))),
                "A triangulation containing t has no internal diagonal incident with its centre 2."),
            Node("phi", "Forward complete chord map", MapFormula(true),
                "Erase t, exchange vertices 1 and 2 in every retained chord, and insert s.", DescribeRole.Definition),
            Node("psi", "Inverse complete chord map", MapFormula(false),
                "Erase s, apply the same vertex exchange, and insert t.", DescribeRole.Definition),
            Node("phi_isTriangulation", "Forward actual triangulation preservation", Preserve(true),
                "Diagonal and crossing preservation use ear-centre exclusion; maximality handles the fresh s separately."),
            Node("psi_isTriangulation", "Inverse actual triangulation preservation", Preserve(false),
                "The inverse preserves the full maximal diagonal carrier."),
            Node("psi_phi", "Left inverse on complete chord sets", Inverse(true),
                "The inverse law requires only diagonal membership and the stated included and excluded ears."),
            Node("phi_psi", "Right inverse on complete chord sets", Inverse(false),
                "This equality holds for the entire finite chord set.")), []));

    private static Formula MapFormula(bool forward) => Scope(All("T", Chords,
        EqF(C(forward ? "phi" : "psi", X("T")), Insert(Ear(forward ? 1 : 2),
            C("image", X("chordSwap"), Erase(X("T"), Ear(forward ? 2 : 1)))))));
    private static Formula Preserve(bool forward) => Scope(All("T", Chords,
        Imp(Lower(6), Imp(Tri(X("T")), Imp(InF(Ear(forward ? 2 : 1), X("T")),
            Tri(C(forward ? "phi" : "psi", X("T"))))))));
    private static Formula Inverse(bool forward) => Scope(All("T", Chords,
        Imp(Lower(6), Imp(Diagonals(X("T")), Imp(InF(Ear(forward ? 2 : 1), X("T")),
            Imp(Not(InF(Ear(forward ? 1 : 2), X("T"))),
                EqF(C(forward ? "psi" : "phi", C(forward ? "phi" : "psi", X("T"))), X("T"))))))));
}
