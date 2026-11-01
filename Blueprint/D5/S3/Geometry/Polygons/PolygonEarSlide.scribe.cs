using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons.PolygonEarSlideFormula;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;

internal sealed class PolygonEarSlideDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Polygons/PolygonEarSlide.";
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("polygon-ear-slide-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual polygon condition preserving ear slide",
        H("Complete exact traces and conditioned fibres"), Blocks(
            Node("EarCenters", "All ears of the actual chord set", Scope(All("T", Chords, All("i", Vertex,
                IffF(InF(X("i"), Ears(X("T"))), InF(C("ear", X("i")), X("T")))))),
                "Every ear of the complete finite chord set is observed.", DescribeRole.Definition),
            Node("E_K", "Common compatible ear carrier", Scope(All("K", Sets, All("i", Vertex,
                IffF(InF(X("i"), C("EK", X("K"))), AndF(Not(InF(X("i"), X("K"))),
                    All("k", Vertex, Imp(InF(X("k"), X("K")), Not(C("Cross", C("ear", X("i")), C("ear", X("k"))))))))))),
                "EK denotes E_K: centres outside K whose ears cross no ear of K.", DescribeRole.Definition),
            Node("ConditionFiber", "Complete conditioned exact-trace fibre", Scope(SetsAll(EqF(
                Fibre(X("J"), X("X")), Seq(OpenBrace, X("T"), Colon, Sp, Chords, Sp, Bar, Sp,
                    AndF(Tri(X("T")), AndF(SubF(X("P"), Ears(X("T"))),
                        AndF(C("Disjoint", X("Q"), Ears(X("T"))), EqF(Inter(Ears(X("T")), X("J")), X("X"))))), CloseBrace)), "P", "Q", "J", "X")),
                "P is forced, Q is forbidden, and the entire observed J trace equals X. The subtype includes infeasible empty fibres.", DescribeRole.Definition),
            Node("isTriangulation_map_add", "Cyclic translation of all triangulations", Scope(All("T", Chords, All("a", Vertex,
                Imp(Tri(X("T")), Tri(C("shiftChords", X("T"), X("a"))))))),
                "shiftChords(T,a) is the finite image of T under the chord map x -> x+a. Diagonal, noncrossing, and maximality conditions are preserved."),
            Node("trace_phi", "Forward exact observed-ear trace", Trace(true),
                "J omits 0 and includes 1,2. R is supported on J with 1,2,3 erased. The output retains exactly R and centre 1 on J with 2,3 erased."),
            Node("trace_psi", "Inverse exact observed-ear trace", Trace(false),
                "The same complete J-origin, membership and R-support hypotheses recover exactly R and centre 2 on the original J."),
            Node("condition_fibre_equiv", "Normalized complete conditioned fibre equivalence", Equivalence(false),
                "J lies in E_K(P union Q), omits 0 and contains 1,2; R lies in J with 1,2,3 erased. All forced and forbidden conditions are preserved. No cardinality, P/Q disjointness or compatibility premise is needed for this local equivalence."),
            Node("condition_fibre_equiv_at", "Complete fibre equivalence at every cyclic origin", Equivalence(true),
                "Conjugation by cyclic translation includes every origin a, the cyclic seam, and empty fibres. The cardinality theorem in PolygonEarSlideCardinality uses this equivalence to count the complete fibres.")), [])));

    private static Formula Trace(bool forward) => Scope(All("T", Chords, SetsAll(
        Imp(Lower(14), Imp(Tri(X("T")), Imp(InF(Ear(forward ? 2 : 1), X("T")),
            LocalHyp(false, Imp(EqF(Inter(Ears(X("T")), forward ? X("J") : Reduced(false)),
                Insert(N(forward ? 2 : 1), X("R"))),
                EqF(Inter(Ears(C(forward ? "phi" : "psi", X("T"))), forward ? Reduced(false) : X("J")),
                    Insert(N(forward ? 1 : 2), X("R")))))))), "J", "R")));
    private static Formula Equivalence(bool cyclic) => Scope(SetsAll(cyclic ? All("a", Vertex, EquivBody(true)) : EquivBody(false), "P", "Q", "J", "R"));
    private static Formula EquivBody(bool cyclic) => Imp(Lower(14), Imp(SubF(X("J"), C("EK", Union(X("P"), X("Q")))),
        LocalHyp(cyclic, C("Equiv", Fibre(X("J"), Insert(Pos(cyclic, 2), X("R"))), Fibre(Reduced(cyclic), Insert(Pos(cyclic, 1), X("R")))))));}
