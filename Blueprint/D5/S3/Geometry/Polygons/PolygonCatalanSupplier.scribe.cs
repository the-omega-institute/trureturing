using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;
internal sealed class PolygonCatalanSupplierDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Support(string name, Formula formula) => Describe.Lean(
        DescribeId.Create("polygon-catalan-supplier-" + name.Replace(".", "-").Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCatalanSupplier." + name.Split('.')[^1]),
        H(name), StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Geometry/axiommath2026polygoncatalan")),
        Blocks(Paragraph(Text("Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged."))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Licensed exact polygon Catalan supplier", H("Complete maximal noncrossing carrier"), Blocks(
        Paragraph(Text("The count-only transplant is from AxiomMath/ClusterAlgebras revision a9174706bce3bcb0fa342b4614f98ef2acb7f91c. Complete license, authors, source spans and hashes, metadata adaptations and receiver-pinned retirement condition are in docs/reports/licenses/cluster-algebras-polygon-third-party.md. This supplies reused enumeration to PolygonConditionalCounts; it supplies no new escape content, actual ear contraction, fan positivity or flip conclusion.")),
        Paragraph(Text("All interval endpoints are integers. pair(i,j) is an ordered integer pair, two(p,q) is its two-element finite set, Ioo(a,b) is the finite open integer interval, and toNat is Int.toNat. Sides(a,b)=intervalSides(a,b), D(a,b)=intervalDiagonals(a,b), Seg(a,b,S)=intervalSegments(a,b,S)=S union Sides(a,b). I(a,b,S)=IsIntervalTriangulation(a,b,S): S subset D(a,b), pairwise noninterleaving, and each missing diagonal in D(a,b) interleaves an S member. tau(a,b)=intervalTriangulationCount(a,b). L(a,b) is the subtype of all S satisfying I(a,b,S), and W(a,b) is the dependent sum over k in Set.Ioo(a,b) of L(a,k) times L(k,b). For an element of W, apex is its integer k, left and right are its two interval triangulations, and val takes the entire underlying finite set.")),
        Paragraph(Text("For polygons, symPair(u,v) is the unordered pair in Sym2(ZMod(m)); Symtwo denotes Sym2. DiagonalSet(m) is the set of all internal diagonals, PolygonTriSet(m) the set of all finite original chord sets satisfying ClusterAlgebras.IsTriangulation, and A(m) the subtype of that entire set. IntervalTriSet(a,b) is the set of all interval triangulations. BijOn includes injection, surjection and mapping into the displayed sets. ENatcard is extended cardinality; coeENat and intCast are the indicated casts. catalanNumber is definitionally Mathlib catalan. The consumer's carrier is identical on whole chord sets, preserving all diagonal, crossing, noncrossing and maximality fields.")),
        Support("catalanNumber_zero",
            EqF(C("catalanNumber", N(0)), N(1))),
        Support("catalanNumber_succ",
            All("N", X("Nat"), EqF(C("catalanNumber", AddF(X("N"), N(1))), SumOver("i", C("range", AddF(X("N"), N(1))), MulF(C("catalanNumber", X("i")), C("catalanNumber", SubF(X("N"), X("i")))))))),
        Support("Interleave.symm",
            All("p", C("Prod", new Formula.Integers(), new Formula.Integers()), All("q", C("Prod", new Formula.Integers(), new Formula.Integers()), Imp(C("Interleave", X("p"), X("q")), C("Interleave", X("q"), X("p")))))),
        Support("mem_intervalTriangulations",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), All("S", C("Finset", C("Prod", new Formula.Integers(), new Formula.Integers())), IffF(InF(X("S"), C("intervalTriangulations", X("a"), X("b"))), C("I", X("a"), X("b"), X("S"))))))),
        Support("mk_mem_intervalDiagonals_iff",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), All("i", new Formula.Integers(), All("j", new Formula.Integers(), IffF(InF(C("pair", X("i"), X("j")), C("D", X("a"), X("b"))), AndF(Le(X("a"), X("i")), Le(X("j"), X("b")), Le(AddF(X("i"), N(2)), X("j")), NotF(AndF(EqF(X("i"), X("a")), EqF(X("j"), X("b"))))))))))),
        Support("mk_mem_intervalSides_iff",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), All("i", new Formula.Integers(), All("j", new Formula.Integers(), IffF(InF(C("pair", X("i"), X("j")), C("Sides", X("a"), X("b"))), OrF(AndF(EqF(X("i"), X("a")), EqF(X("j"), X("b"))), AndF(Le(X("a"), X("i")), Lt(X("i"), X("b")), EqF(X("j"), AddF(X("i"), N(1))))))))))),
        Support("not_interleave_of_mem_intervalSides",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), All("i", new Formula.Integers(), All("j", new Formula.Integers(), All("k", new Formula.Integers(), All("l", new Formula.Integers(), Imp(InF(C("pair", X("i"), X("j")), C("Sides", X("a"), X("b"))), Imp(Le(X("a"), X("k")), Imp(Le(X("l"), X("b")), NotF(C("Interleave", C("pair", X("i"), X("j")), C("pair", X("k"), X("l")))))))))))))),
        Support("IsIntervalTriangulation.bounds_of_mem_intervalSegments",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), All("S", C("Finset", C("Prod", new Formula.Integers(), new Formula.Integers())), Imp(Lt(X("a"), X("b")), Imp(C("I", X("a"), X("b"), X("S")), All("i", new Formula.Integers(), All("j", new Formula.Integers(), Imp(InF(C("pair", X("i"), X("j")), C("Seg", X("a"), X("b"), X("S"))), AndF(Le(X("a"), X("i")), Lt(X("i"), X("j")), Le(X("j"), X("b")))))))))))),
        Support("IsIntervalTriangulation.not_interleave",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), All("S", C("Finset", C("Prod", new Formula.Integers(), new Formula.Integers())), Imp(Lt(X("a"), X("b")), Imp(C("I", X("a"), X("b"), X("S")), All("p", C("Prod", new Formula.Integers(), new Formula.Integers()), All("q", C("Prod", new Formula.Integers(), new Formula.Integers()), Imp(InF(X("p"), C("Seg", X("a"), X("b"), X("S"))), Imp(InF(X("q"), C("Seg", X("a"), X("b"), X("S"))), NotF(C("Interleave", X("p"), X("q"))))))))))))),
        Support("IsIntervalTriangulation.exists_interleave",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), All("S", C("Finset", C("Prod", new Formula.Integers(), new Formula.Integers())), Imp(Lt(X("a"), X("b")), Imp(C("I", X("a"), X("b"), X("S")), All("i", new Formula.Integers(), All("j", new Formula.Integers(), Imp(Le(X("a"), X("i")), Imp(Lt(X("i"), X("j")), Imp(Le(X("j"), X("b")), Imp(NotF(InF(C("pair", X("i"), X("j")), C("Seg", X("a"), X("b"), X("S")))), Ex("q", C("Prod", new Formula.Integers(), new Formula.Integers()), AndF(InF(X("q"), X("S")), C("Interleave", C("pair", X("i"), X("j")), X("q")))))))))))))))),
        Support("IsIntervalTriangulation.existsUnique_apex",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), All("S", C("Finset", C("Prod", new Formula.Integers(), new Formula.Integers())), Imp(Lt(X("a"), X("b")), Imp(C("I", X("a"), X("b"), X("S")), All("i", new Formula.Integers(), All("k", new Formula.Integers(), Imp(Le(AddF(X("i"), N(2)), X("k")), Imp(InF(C("pair", X("i"), X("k")), C("Seg", X("a"), X("b"), X("S"))), Ex("j", new Formula.Integers(), AndF(AndF(Lt(X("i"), X("j")), Lt(X("j"), X("k")), InF(C("pair", X("i"), X("j")), C("Seg", X("a"), X("b"), X("S"))), InF(C("pair", X("j"), X("k")), C("Seg", X("a"), X("b"), X("S")))), All("z", new Formula.Integers(), Imp(AndF(Lt(X("i"), X("z")), Lt(X("z"), X("k")), InF(C("pair", X("i"), X("z")), C("Seg", X("a"), X("b"), X("S"))), InF(C("pair", X("z"), X("k")), C("Seg", X("a"), X("b"), X("S")))), EqF(X("z"), X("j")))))))))))))))),
        Support("IsIntervalTriangulation.le_or_le_of_apex",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), All("S", C("Finset", C("Prod", new Formula.Integers(), new Formula.Integers())), Imp(Lt(X("a"), X("b")), Imp(C("I", X("a"), X("b"), X("S")), All("k", new Formula.Integers(), Imp(InF(C("pair", X("a"), X("k")), C("Seg", X("a"), X("b"), X("S"))), Imp(InF(C("pair", X("k"), X("b")), C("Seg", X("a"), X("b"), X("S"))), All("i", new Formula.Integers(), All("j", new Formula.Integers(), Imp(InF(C("pair", X("i"), X("j")), X("S")), OrF(Le(X("j"), X("k")), Le(X("k"), X("i"))))))))))))))),
        Support("IsIntervalTriangulation.eq_union_of_apex",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), All("S", C("Finset", C("Prod", new Formula.Integers(), new Formula.Integers())), Imp(Lt(X("a"), X("b")), Imp(C("I", X("a"), X("b"), X("S")), All("k", new Formula.Integers(), Imp(Lt(X("a"), X("k")), Imp(Lt(X("k"), X("b")), Imp(InF(C("pair", X("a"), X("k")), C("Seg", X("a"), X("b"), X("S"))), Imp(InF(C("pair", X("k"), X("b")), C("Seg", X("a"), X("b"), X("S"))), EqF(X("S"), C("union", C("union", C("inter", X("S"), C("D", X("a"), X("k"))), C("inter", X("S"), C("D", X("k"), X("b")))), C("inter", C("two", C("pair", X("a"), X("k")), C("pair", X("k"), X("b"))), C("D", X("a"), X("b")))))))))))))))),
        Support("IsIntervalTriangulation.inter_left_of_apex",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), All("S", C("Finset", C("Prod", new Formula.Integers(), new Formula.Integers())), Imp(Lt(X("a"), X("b")), Imp(C("I", X("a"), X("b"), X("S")), All("k", new Formula.Integers(), Imp(Lt(X("k"), X("b")), Imp(InF(C("pair", X("a"), X("k")), C("Seg", X("a"), X("b"), X("S"))), Imp(InF(C("pair", X("k"), X("b")), C("Seg", X("a"), X("b"), X("S"))), C("I", X("a"), X("k"), C("inter", X("S"), C("D", X("a"), X("k")))))))))))))),
        Support("IsIntervalTriangulation.inter_right_of_apex",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), All("S", C("Finset", C("Prod", new Formula.Integers(), new Formula.Integers())), Imp(Lt(X("a"), X("b")), Imp(C("I", X("a"), X("b"), X("S")), All("k", new Formula.Integers(), Imp(Lt(X("a"), X("k")), Imp(InF(C("pair", X("a"), X("k")), C("Seg", X("a"), X("b"), X("S"))), Imp(InF(C("pair", X("k"), X("b")), C("Seg", X("a"), X("b"), X("S"))), C("I", X("k"), X("b"), C("inter", X("S"), C("D", X("k"), X("b")))))))))))))),
        Support("mk_mem_union_intervalDiagonals_iff",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), All("k", new Formula.Integers(), All("Sone", C("Finset", C("Prod", new Formula.Integers(), new Formula.Integers())), All("Stwo", C("Finset", C("Prod", new Formula.Integers(), new Formula.Integers())), All("i", new Formula.Integers(), All("j", new Formula.Integers(), IffF(InF(C("pair", X("i"), X("j")), C("union", C("union", X("Sone"), X("Stwo")), C("inter", C("two", C("pair", X("a"), X("k")), C("pair", X("k"), X("b"))), C("D", X("a"), X("b"))))), OrF(InF(C("pair", X("i"), X("j")), X("Sone")), InF(C("pair", X("i"), X("j")), X("Stwo")), AndF(OrF(AndF(EqF(X("i"), X("a")), EqF(X("j"), X("k"))), AndF(EqF(X("i"), X("k")), EqF(X("j"), X("b")))), InF(C("pair", X("i"), X("j")), C("D", X("a"), X("b")))))))))))))),
        Support("IsIntervalTriangulation.union",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), All("k", new Formula.Integers(), All("Sone", C("Finset", C("Prod", new Formula.Integers(), new Formula.Integers())), All("Stwo", C("Finset", C("Prod", new Formula.Integers(), new Formula.Integers())), Imp(Lt(X("a"), X("k")), Imp(Lt(X("k"), X("b")), Imp(C("I", X("a"), X("k"), X("Sone")), Imp(C("I", X("k"), X("b"), X("Stwo")), C("I", X("a"), X("b"), C("union", C("union", X("Sone"), X("Stwo")), C("inter", C("two", C("pair", X("a"), X("k")), C("pair", X("k"), X("b"))), C("D", X("a"), X("b"))))))))))))))),
        Support("union_inter_intervalDiagonals_left",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), All("k", new Formula.Integers(), All("Sone", C("Finset", C("Prod", new Formula.Integers(), new Formula.Integers())), All("Stwo", C("Finset", C("Prod", new Formula.Integers(), new Formula.Integers())), Imp(C("I", X("a"), X("k"), X("Sone")), Imp(C("I", X("k"), X("b"), X("Stwo")), EqF(C("inter", C("union", C("union", X("Sone"), X("Stwo")), C("inter", C("two", C("pair", X("a"), X("k")), C("pair", X("k"), X("b"))), C("D", X("a"), X("b")))), C("D", X("a"), X("k"))), X("Sone")))))))))),
        Support("union_inter_intervalDiagonals_right",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), All("k", new Formula.Integers(), All("Sone", C("Finset", C("Prod", new Formula.Integers(), new Formula.Integers())), All("Stwo", C("Finset", C("Prod", new Formula.Integers(), new Formula.Integers())), Imp(Lt(X("a"), X("k")), Imp(C("I", X("a"), X("k"), X("Sone")), Imp(C("I", X("k"), X("b"), X("Stwo")), EqF(C("inter", C("union", C("union", X("Sone"), X("Stwo")), C("inter", C("two", C("pair", X("a"), X("k")), C("pair", X("k"), X("b"))), C("D", X("a"), X("b")))), C("D", X("k"), X("b"))), X("Stwo"))))))))))),
        Support("union_apex_mem_intervalSegments",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), All("k", new Formula.Integers(), All("Sone", C("Finset", C("Prod", new Formula.Integers(), new Formula.Integers())), All("Stwo", C("Finset", C("Prod", new Formula.Integers(), new Formula.Integers())), Imp(Lt(X("a"), X("k")), Imp(Lt(X("k"), X("b")), AndF(InF(C("pair", X("a"), X("k")), C("Seg", X("a"), X("b"), C("union", C("union", X("Sone"), X("Stwo")), C("inter", C("two", C("pair", X("a"), X("k")), C("pair", X("k"), X("b"))), C("D", X("a"), X("b")))))), InF(C("pair", X("k"), X("b")), C("Seg", X("a"), X("b"), C("union", C("union", X("Sone"), X("Stwo")), C("inter", C("two", C("pair", X("a"), X("k")), C("pair", X("k"), X("b"))), C("D", X("a"), X("b"))))))))))))))),
        Support("exists_equiv_intervalTriangulation",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), Imp(Le(AddF(X("a"), N(2)), X("b")), Ex("e", C("Equiv", C("L", X("a"), X("b")), C("W", X("a"), X("b"))), All("S", C("L", X("a"), X("b")), AndF(InF(C("pair", X("a"), C("apex", C("app", X("e"), X("S")))), C("Seg", X("a"), X("b"), C("val", X("S")))), InF(C("pair", C("apex", C("app", X("e"), X("S"))), X("b")), C("Seg", X("a"), X("b"), C("val", X("S")))), EqF(C("val", C("left", C("app", X("e"), X("S")))), C("inter", C("val", X("S")), C("D", X("a"), C("apex", C("app", X("e"), X("S")))))), EqF(C("val", C("right", C("app", X("e"), X("S")))), C("inter", C("val", X("S")), C("D", C("apex", C("app", X("e"), X("S"))), X("b"))))))))))),
        Support("card_subtype_isIntervalTriangulation",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), EqF(C("Fintypecard", C("L", X("a"), X("b"))), C("tau", X("a"), X("b")))))),
        Support("intervalTriangulationCount_eq_sum",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), Imp(Le(AddF(X("a"), N(2)), X("b")), EqF(C("tau", X("a"), X("b")), SumOver("k", C("Ioo", X("a"), X("b")), MulF(C("tau", X("a"), X("k")), C("tau", X("k"), X("b"))))))))),
        Support("intervalTriangulationCount_self_add_one",
            All("a", new Formula.Integers(), EqF(C("tau", X("a"), AddF(X("a"), N(1))), N(1)))),
        Support("intervalTriangulationCount_eq_catalanNumber",
            All("a", new Formula.Integers(), All("b", new Formula.Integers(), Imp(Lt(X("a"), X("b")), EqF(C("tau", X("a"), X("b")), C("catalanNumber", C("toNat", SubF(SubF(X("b"), X("a")), N(1))))))))),
        Support("basePosSeg_mk",
            All("m", X("Nat"), All("c", C("ZMod", X("m")), All("u", C("ZMod", X("m")), All("v", C("ZMod", X("m")), EqF(C("basePosSeg", X("c"), C("symPair", X("u"), X("v"))), C("pair", C("min", C("basePos", X("c"), X("u")), C("basePos", X("c"), X("v"))), C("max", C("basePos", X("c"), X("u")), C("basePos", X("c"), X("v")))))))))),
        Support("basePos_nonneg",
            All("m", X("Nat"), All("c", C("ZMod", X("m")), All("v", C("ZMod", X("m")), Le(N(0), C("basePos", X("c"), X("v"))))))),
        Support("basePos_lt",
            All("m", X("Nat"), Inst(C("NeZero", X("m")), All("c", C("ZMod", X("m")), All("v", C("ZMod", X("m")), Lt(C("basePos", X("c"), X("v")), C("intCast", X("m")))))))),
        Support("basePos_eq_ite",
            All("m", X("Nat"), Inst(C("NeZero", X("m")), All("c", C("ZMod", X("m")), All("v", C("ZMod", X("m")), EqF(C("basePos", X("c"), X("v")), C("ite", Le(C("val", X("c")), C("val", X("v"))), SubF(C("intCast", C("val", X("v"))), C("intCast", C("val", X("c")))), AddF(SubF(C("intCast", C("val", X("v"))), C("intCast", C("val", X("c")))), C("intCast", X("m")))))))))),
        Support("basePos_injective",
            All("m", X("Nat"), Inst(C("NeZero", X("m")), All("c", C("ZMod", X("m")), C("Injective", C("basePos", X("c"))))))),
        Support("exists_basePos_eq",
            All("m", X("Nat"), All("c", C("ZMod", X("m")), All("k", new Formula.Integers(), Imp(Le(N(0), X("k")), Imp(Lt(X("k"), C("intCast", X("m"))), Ex("v", C("ZMod", X("m")), EqF(C("basePos", X("c"), X("v")), X("k"))))))))),
        Support("sbtw_iff_val",
            All("m", X("Nat"), Inst(C("NeZero", X("m")), All("x", C("ZMod", X("m")), All("y", C("ZMod", X("m")), All("z", C("ZMod", X("m")), IffF(C("sbtw", X("x"), X("y"), X("z")), OrF(AndF(Lt(C("val", X("x")), C("val", X("y"))), Lt(C("val", X("y")), C("val", X("z")))), AndF(Lt(C("val", X("y")), C("val", X("z"))), Lt(C("val", X("z")), C("val", X("x")))), AndF(Lt(C("val", X("z")), C("val", X("x"))), Lt(C("val", X("x")), C("val", X("y")))))))))))),
        Support("sbtw_iff_sbtw_basePos",
            All("m", X("Nat"), Inst(C("NeZero", X("m")), All("c", C("ZMod", X("m")), All("u", C("ZMod", X("m")), All("x", C("ZMod", X("m")), All("v", C("ZMod", X("m")), IffF(C("sbtw", X("u"), X("x"), X("v")), C("sbtw", C("basePos", X("c"), X("u")), C("basePos", X("c"), X("x")), C("basePos", X("c"), X("v"))))))))))),
        Support("basePos_add_one",
            All("m", X("Nat"), Inst(C("NeZero", X("m")), All("c", C("ZMod", X("m")), All("u", C("ZMod", X("m")), EqF(C("basePos", X("c"), AddF(X("u"), N(1))), C("ite", EqF(AddF(C("basePos", X("c"), X("u")), N(1)), C("intCast", X("m"))), N(0), AddF(C("basePos", X("c"), X("u")), N(1))))))))),
        Support("basePosSeg_injective",
            All("m", X("Nat"), Inst(C("NeZero", X("m")), All("c", C("ZMod", X("m")), C("Injective", C("basePosSeg", X("c"))))))),
        Support("IsSegment.exists_basePos_lt",
            All("m", X("Nat"), Inst(C("NeZero", X("m")), All("c", C("ZMod", X("m")), All("s", C("Symtwo", C("ZMod", X("m"))), Imp(C("IsSegment", X("s")), Ex("u", C("ZMod", X("m")), Ex("v", C("ZMod", X("m")), AndF(EqF(X("s"), C("symPair", X("u"), X("v"))), Lt(C("basePos", X("c"), X("u")), C("basePos", X("c"), X("v")))))))))))),
        Support("basePosSeg_mk_of_lt",
            All("m", X("Nat"), All("c", C("ZMod", X("m")), All("u", C("ZMod", X("m")), All("v", C("ZMod", X("m")), Imp(Lt(C("basePos", X("c"), X("u")), C("basePos", X("c"), X("v"))), EqF(C("basePosSeg", X("c"), C("symPair", X("u"), X("v"))), C("pair", C("basePos", X("c"), X("u")), C("basePos", X("c"), X("v")))))))))),
        Support("isSide_mk_iff",
            All("m", X("Nat"), All("u", C("ZMod", X("m")), All("v", C("ZMod", X("m")), IffF(C("IsSide", C("symPair", X("u"), X("v"))), OrF(EqF(X("v"), AddF(X("u"), N(1))), EqF(X("u"), AddF(X("v"), N(1))))))))),
        Support("cross_mk_iff",
            All("m", X("Nat"), All("u", C("ZMod", X("m")), All("v", C("ZMod", X("m")), All("x", C("ZMod", X("m")), All("y", C("ZMod", X("m")), IffF(C("Cross", C("symPair", X("u"), X("v")), C("symPair", X("x"), X("y"))), OrF(AndF(C("sbtw", X("u"), X("x"), X("v")), C("sbtw", X("v"), X("y"), X("u"))), AndF(C("sbtw", X("u"), X("y"), X("v")), C("sbtw", X("v"), X("x"), X("u"))))))))))),
        Support("cross_mk_iff_basePos",
            All("m", X("Nat"), Inst(C("NeZero", X("m")), All("c", C("ZMod", X("m")), All("u", C("ZMod", X("m")), All("v", C("ZMod", X("m")), All("x", C("ZMod", X("m")), All("y", C("ZMod", X("m")), IffF(C("Cross", C("symPair", X("u"), X("v")), C("symPair", X("x"), X("y"))), OrF(AndF(C("sbtw", C("basePos", X("c"), X("u")), C("basePos", X("c"), X("x")), C("basePos", X("c"), X("v"))), C("sbtw", C("basePos", X("c"), X("v")), C("basePos", X("c"), X("y")), C("basePos", X("c"), X("u")))), AndF(C("sbtw", C("basePos", X("c"), X("u")), C("basePos", X("c"), X("y")), C("basePos", X("c"), X("v"))), C("sbtw", C("basePos", X("c"), X("v")), C("basePos", X("c"), X("x")), C("basePos", X("c"), X("u")))))))))))))),
        Support("isSide_mk_iff_basePos",
            All("m", X("Nat"), Inst(C("NeZero", X("m")), All("c", C("ZMod", X("m")), All("u", C("ZMod", X("m")), All("v", C("ZMod", X("m")), Imp(Lt(C("basePos", X("c"), X("u")), C("basePos", X("c"), X("v"))), IffF(C("IsSide", C("symPair", X("u"), X("v"))), OrF(EqF(C("basePos", X("c"), X("v")), AddF(C("basePos", X("c"), X("u")), N(1))), AndF(EqF(C("basePos", X("c"), X("u")), N(0)), EqF(C("basePos", X("c"), X("v")), SubF(C("intCast", X("m")), N(1))))))))))))),
        Support("bijOn_basePosSeg_isDiagonal",
            All("m", X("Nat"), Inst(C("NeZero", X("m")), All("c", C("ZMod", X("m")), C("BijOn", C("basePosSeg", X("c")), C("DiagonalSet", X("m")), C("coeSet", C("D", N(0), SubF(C("intCast", X("m")), N(1))))))))),
        Support("cross_iff_interleave",
            All("m", X("Nat"), Inst(C("NeZero", X("m")), All("c", C("ZMod", X("m")), All("s", C("Symtwo", C("ZMod", X("m"))), All("t", C("Symtwo", C("ZMod", X("m"))), Imp(C("IsSegment", X("s")), Imp(C("IsSegment", X("t")), IffF(C("Cross", X("s"), X("t")), C("Interleave", C("basePosSeg", X("c"), X("s")), C("basePosSeg", X("c"), X("t")))))))))))),
        Support("bijOn_basePosTri",
            All("m", X("Nat"), Inst(C("NeZero", X("m")), All("c", C("ZMod", X("m")), C("BijOn", C("basePosTri", X("c")), C("PolygonTriSet", X("m")), C("IntervalTriSet", N(0), SubF(C("intCast", X("m")), N(1)))))))),
        Support("encard_setOf_isTriangulation",
            All("m", X("Nat"), Inst(C("NeZero", X("m")), Imp(Le(N(3), X("m")), EqF(C("ENatcard", C("A", X("m"))), C("coeENat", C("catalanNumber", SubF(X("m"), N(2)))))))))
        ), []));
    private static Formula X(string n) => F.Id(n);
    private static Formula N(byte n) => D(n);
    private static Formula C(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname,Grp(X(n))), [.. args]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),t,b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(n),t,b);
    private static Formula Inst(Formula t, Formula b) => Seq(OpenBracket,t,CloseBracket,Comma,Sp,b);
    private static Formula Operand(Formula f) => f is Formula.Bind ? Seq(Open,f,Close) : f;
    private static Formula R(Formula a, Formula op, Formula b) => Seq(Open,Operand(a),Sp,op,Sp,Operand(b),Close);
    private static Formula EqF(Formula a, Formula b) => R(a,F.Eq,b);
    private static Formula IffF(Formula a, Formula b) => R(a,F.Iff,b);
    private static Formula Imp(Formula a, Formula b) => R(a,Implies,b);
    private static Formula AndF(params Formula[] a) => Fold(a,Land);
    private static Formula OrF(params Formula[] a) => Fold(a,Lor);
    private static Formula Fold(Formula[] a, Formula op) { var b=a[^1]; for(int i=a.Length-2;i>=0;i--) b=R(a[i],op,b); return b; }
    private static Formula NotF(Formula a) => Seq(Neg,Sp,Open,a,Close);
    private static Formula InF(Formula a, Formula b) => R(a,InMacro,b);
    private static Formula Le(Formula a, Formula b) => R(a,Leq,b);
    private static Formula Lt(Formula a, Formula b) => R(a,F.Lt,b);
    private static Formula AddF(Formula a, Formula b) => R(a,Plus,b);
    private static Formula SubF(Formula a, Formula b) => R(a,Minus,b);
    private static Formula MulF(Formula a, Formula b) => R(a,Cdot,b);
    private static Formula SumOver(string n, Formula domain, Formula body) => Seq(Sum,Sp,Underscore,Grp(X(n),InMacro,Sp,domain),Sp,Open,body,Close);
}
