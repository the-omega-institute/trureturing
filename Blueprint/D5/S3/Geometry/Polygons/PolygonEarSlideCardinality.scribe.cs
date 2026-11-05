using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons.PolygonEarSlideCardinalityFormula;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;

internal sealed class PolygonEarSlideCardinalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact complete-fibre local polygon ear-slide counts",
        H("Complete conditioned fibres at every cyclic block origin"),
        Blocks(Describe.Lean(DescribeId.Create("polygon-ear-slide-cardinality-at"),
            DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonEarSlideCardinality.condition_fibre_card_at"),
            H("Exact local law with the optional third-ear fibre"), StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("For n at least 14, P and Q are arbitrary forced and forbidden ear-centre sets. J is a subset of E_K(P union Q), a is absent from J, and a+1,a+2 belong to J. R is supported on J with a+1,a+2,a+3 erased. Nat.card counts the complete ConditionFiber subtype of actual maximal noncrossing finite diagonal sets. Thus infeasible and empty fibres are included.")),
                Paragraph(Text("Write s=a+1, t=a+2, u=a+3. The complete fibre with trace R+t is equivalent, by condition_fibre_equiv_at, to the fibre with trace R+s on J with t,u erased. Every member of that reduced fibre contains s and therefore excludes t, since those actual ears cross. Restoring the observations in J leaves only the choice whether u occurs. When u belongs to J, the two disjoint branches are exactly the original full fibres with traces R+s and R+s+u. Otherwise there is just the R+s fibre. Both branch maps preserve the entire original chord set, P, and Q.")),
                Paragraph(Text("This is the local complete-count law (37.8) of the pinned theory AURIC_FIB_ATOM_INTRINSIC_CLASSIFICATION_AND_POLYGON_GEOMETRY, B-37.2, at source revision 7a72936968c08198f04951d1326bfd4dd891e804. The four source cases (|P|,|Q|)=(2,2),(3,3),(2,4),(4,2), with disjoint compatible P,Q, are special cases; these extra restrictions are unnecessary for the local law. Exchanging P and Q gives a separate instance using E_K(Q union P)=E_K(P union Q). No equality between the two sides' weights is asserted or used.")),
                Paragraph(Text("The result supplies neither global conditional-count positivity, normalized strict inequality or its equality case, nor terminal independent nonempty support. It does not formalize the remainder of B-37.2. Natcard in the formula denotes Nat.card, and ite(c,x,y) means x if c holds and y otherwise; EK in the companion document denotes E_K."))), DescribeRole.Theorem)), []));

    private static Formula Count(Formula trace) => C("Natcard", Fibre(X("J"), trace));
    private static Formula Statement() => Scope(All("a", Vertex, SetsAll(
        Imp(Lower(14), Imp(SubF(X("J"), C("EK", Union(X("P"), X("Q")))), LocalHyp(true,
            EqF(Count(Insert(Pos(true, 2), X("R"))),
                AddF(Count(Insert(Pos(true, 1), X("R"))),
                    C("ite", InF(Pos(true, 3), X("J")),
                        Count(Insert(Pos(true, 3), Insert(Pos(true, 1), X("R")))), N(0))))))),
        "P", "Q", "J", "R")));
}

internal static class PolygonEarSlideCardinalityFormula
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
