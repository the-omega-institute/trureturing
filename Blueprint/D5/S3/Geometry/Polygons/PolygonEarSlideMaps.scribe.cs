using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons.PolygonEarSlideMapsFormula;

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

internal static class PolygonEarSlideMapsFormula
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
