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
                "Conjugation by cyclic translation includes every origin a, the cyclic seam, and empty fibres. The cardinality theorem in PolygonEarSlideCardinality uses this equivalence to count the complete fibres.")), []));

    private static Formula Trace(bool forward) => Scope(All("T", Chords, SetsAll(
        Imp(Lower(14), Imp(Tri(X("T")), Imp(InF(Ear(forward ? 2 : 1), X("T")),
            LocalHyp(false, Imp(EqF(Inter(Ears(X("T")), forward ? X("J") : Reduced(false)),
                Insert(N(forward ? 2 : 1), X("R"))),
                EqF(Inter(Ears(C(forward ? "phi" : "psi", X("T"))), forward ? Reduced(false) : X("J")),
                    Insert(N(forward ? 1 : 2), X("R")))))))), "J", "R")));
    private static Formula Equivalence(bool cyclic) => Scope(SetsAll(cyclic ? All("a", Vertex, EquivBody(true)) : EquivBody(false), "P", "Q", "J", "R"));
    private static Formula EquivBody(bool cyclic) => Imp(Lower(14), Imp(SubF(X("J"), C("EK", Union(X("P"), X("Q")))),
        LocalHyp(cyclic, C("Equiv", Fibre(X("J"), Insert(Pos(cyclic, 2), X("R"))), Fibre(Reduced(cyclic), Insert(Pos(cyclic, 1), X("R")))))));}

internal static class PolygonEarSlideFormula
{
    internal static Formula X(string name) => F.Id(name);
    internal static Formula N(int n) => n == 14 ? D(1,4) : D((byte)n);
    internal static Formula C(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(X(name))), [.. args]);
    internal static Formula Vertex => C("ZMod", X("n"));
    internal static Formula Chord => new Formula.Apply(Seq(Operatorname, Grp(X("Sym"), D(2))), [Vertex]);
    internal static Formula Sets => C("Finset", Vertex);
    internal static Formula Chords => C("Finset", Chord);
    internal static Formula All(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    internal static Formula ExistsF(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), domain, body);
    internal static Formula Scope(Formula body) => All("n", X("Nat"), Seq(OpenBracket, C("NeZero", X("n")), CloseBracket, Comma, Sp, body));
    internal static Formula SetsAll(Formula body, params string[] names) { for (int i = names.Length - 1; i >= 0; i--) body = All(names[i], Sets, body); return body; }
    private static Formula Operand(Formula f) => f is Formula.Bind ? Seq(Open, f, Close) : f;
    internal static Formula R(Formula a, Formula op, Formula b) => Seq(Open, Operand(a), Sp, op, Sp, Operand(b), Close);
    internal static Formula EqF(Formula a, Formula b) => R(a, F.Eq, b);
    internal static Formula IffF(Formula a, Formula b) => R(a, F.Iff, b);
    internal static Formula AndF(Formula a, Formula b) => R(a, Land, b);
    internal static Formula Imp(Formula a, Formula b) => R(a, Implies, b);
    internal static Formula Not(Formula a) => Seq(Neg, Sp, Open, a, Close);
    internal static Formula InF(Formula a, Formula b) => R(a, InMacro, b);
    internal static Formula SubF(Formula a, Formula b) => R(a, Subseteq, b);
    internal static Formula AddF(Formula a, Formula b) => R(a, Plus, b);
    internal static Formula Sub(Formula a, Formula b) => R(a, Minus, b);
    internal static Formula Union(Formula a, Formula b) => R(a, Cup, b);
    internal static Formula Inter(Formula a, Formula b) => C("inter", a, b);
    internal static Formula Erase(Formula a, Formula b) => C("erase", a, b);
    internal static Formula Insert(Formula a, Formula b) => C("insert", a, b);
    internal static Formula Pair(Formula a, Formula b) => C("symPair", a, b);
    internal static Formula Ear(int i) => C("ear", N(i));
    internal static Formula Ears(Formula t) => C("EarCenters", t);
    internal static Formula Tri(Formula t) => C("IsTriangulation", t);
    internal static Formula Diagonals(Formula t) => All("e", Chord, Imp(InF(X("e"), t), C("IsDiagonal", X("e"))));
    internal static Formula Fibre(Formula j, Formula r) => C("ConditionFiber", X("P"), X("Q"), j, r);
    internal static Formula Lower(int n) => R(N(n), Leq, X("n"));
    internal static Formula Pos(bool cyclic, int i) => cyclic ? (i == 0 ? X("a") : AddF(X("a"), N(i))) : N(i);
    internal static Formula Reduced(bool cyclic) => Erase(Erase(X("J"), Pos(cyclic, 2)), Pos(cyclic, 3));
    internal static Formula LocalHyp(bool cyclic, Formula body) => Imp(Not(InF(Pos(cyclic, 0), X("J"))),
        Imp(InF(Pos(cyclic, 1), X("J")), Imp(InF(Pos(cyclic, 2), X("J")),
            Imp(SubF(X("R"), Erase(Erase(Erase(X("J"), Pos(cyclic, 1)), Pos(cyclic, 2)), Pos(cyclic, 3))), body))));
}
