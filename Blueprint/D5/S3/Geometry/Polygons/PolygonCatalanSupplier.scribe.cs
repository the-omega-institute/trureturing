using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;
internal sealed class PolygonCatalanSupplierDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Support(string name) => Describe.Lean(
        DescribeId.Create("polygon-catalan-supplier-" + name.Replace(".", "-").Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCatalanSupplier." + name),
        H(name), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text("Exact licensed source support on the consumed polygon-count proof path. The complete compiled telescope is displayed without changing its assumptions."))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Licensed exact polygon Catalan supplier", H("Complete maximal noncrossing carrier"), Blocks(
        Paragraph(Text("This count-only transplant comes from AxiomMath/ClusterAlgebras revision a9174706bce3bcb0fa342b4614f98ef2acb7f91c. Complete license, author attribution, source spans and hashes, metadata adaptations and receiver-pinned retirement condition are in docs/reports/licenses/cluster-algebras-polygon-third-party.md. No source proof body is rewritten. It supplies enumeration to PolygonConditionalCounts; it is reused mathematics rather than new escape content.")),
        Describe.Lean(DescribeId.Create("polygon-catalan-supplier-count"),
            DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCatalanSupplier.ClusterAlgebras.TypeA.encard_setOf_isTriangulation"),
            H("All polygon triangulations"), StatementSource.FromAuthor(Disp(Count())), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A(m) denotes the subtype of every finite unordered original chord set satisfying ClusterAlgebras.IsTriangulation: all chords internal, no crossings, and every missing internal diagonal crossed. ENatcard is ENat.card; the Catalan value is coerced to the extended natural numbers. The receiver's existing carrier has the same definitions, and the consumer identifies these subtypes by the identity on the entire chord set. Interval decomposition and cyclic-order linearization supply the imported count. No ear contraction, fan positivity or flip result is supplied here."))), DescribeRole.Theorem),
        Support("ClusterAlgebras.catalanNumber_zero"),
        Support("ClusterAlgebras.catalanNumber_succ"),
        Support("ClusterAlgebras.TypeA.Interleave.symm"),
        Support("ClusterAlgebras.TypeA.mem_intervalTriangulations"),
        Support("ClusterAlgebras.TypeA.mk_mem_intervalDiagonals_iff"),
        Support("ClusterAlgebras.TypeA.mk_mem_intervalSides_iff"),
        Support("ClusterAlgebras.TypeA.not_interleave_of_mem_intervalSides"),
        Support("ClusterAlgebras.TypeA.IsIntervalTriangulation.bounds_of_mem_intervalSegments"),
        Support("ClusterAlgebras.TypeA.IsIntervalTriangulation.not_interleave"),
        Support("ClusterAlgebras.TypeA.IsIntervalTriangulation.exists_interleave"),
        Support("ClusterAlgebras.TypeA.IsIntervalTriangulation.existsUnique_apex"),
        Support("ClusterAlgebras.TypeA.IsIntervalTriangulation.le_or_le_of_apex"),
        Support("ClusterAlgebras.TypeA.IsIntervalTriangulation.eq_union_of_apex"),
        Support("ClusterAlgebras.TypeA.IsIntervalTriangulation.inter_left_of_apex"),
        Support("ClusterAlgebras.TypeA.IsIntervalTriangulation.inter_right_of_apex"),
        Support("ClusterAlgebras.TypeA.mk_mem_union_intervalDiagonals_iff"),
        Support("ClusterAlgebras.TypeA.IsIntervalTriangulation.union"),
        Support("ClusterAlgebras.TypeA.union_inter_intervalDiagonals_left"),
        Support("ClusterAlgebras.TypeA.union_inter_intervalDiagonals_right"),
        Support("ClusterAlgebras.TypeA.union_apex_mem_intervalSegments"),
        Support("ClusterAlgebras.TypeA.exists_equiv_intervalTriangulation"),
        Support("ClusterAlgebras.TypeA.card_subtype_isIntervalTriangulation"),
        Support("ClusterAlgebras.TypeA.intervalTriangulationCount_eq_sum"),
        Support("ClusterAlgebras.TypeA.intervalTriangulationCount_self_add_one"),
        Support("ClusterAlgebras.TypeA.intervalTriangulationCount_eq_catalanNumber"),
        Support("ClusterAlgebras.TypeA.basePosSeg_mk"),
        Support("ClusterAlgebras.TypeA.basePos_nonneg"),
        Support("ClusterAlgebras.TypeA.basePos_lt"),
        Support("ClusterAlgebras.TypeA.basePos_eq_ite"),
        Support("ClusterAlgebras.TypeA.basePos_injective"),
        Support("ClusterAlgebras.TypeA.exists_basePos_eq"),
        Support("ClusterAlgebras.TypeA.sbtw_iff_val"),
        Support("ClusterAlgebras.TypeA.sbtw_iff_sbtw_basePos"),
        Support("ClusterAlgebras.TypeA.basePos_add_one"),
        Support("ClusterAlgebras.TypeA.basePosSeg_injective"),
        Support("ClusterAlgebras.TypeA.IsSegment.exists_basePos_lt"),
        Support("ClusterAlgebras.TypeA.basePosSeg_mk_of_lt"),
        Support("ClusterAlgebras.TypeA.isSide_mk_iff"),
        Support("ClusterAlgebras.TypeA.cross_mk_iff"),
        Support("ClusterAlgebras.TypeA.cross_mk_iff_basePos"),
        Support("ClusterAlgebras.TypeA.isSide_mk_iff_basePos"),
        Support("ClusterAlgebras.TypeA.bijOn_basePosSeg_isDiagonal"),
        Support("ClusterAlgebras.TypeA.cross_iff_interleave"),
        Support("ClusterAlgebras.TypeA.bijOn_basePosTri")
        ), []));
    private static Formula X(string n) => F.Id(n);
    private static Formula C(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname,Grp(X(n))), [.. args]);
    private static Formula R(Formula a, Formula op, Formula b) => Seq(Open,a,Sp,op,Sp,b,Close);
    private static Formula Count() => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("m"), X("Nat"),
        Seq(OpenBracket,C("NeZero",X("m")),CloseBracket,Comma,Sp,
            R(R(D(3),Leq,X("m")),Implies,
                R(C("ENatcard", C("A",X("m"))),F.Eq,
                    C("coeENat", C("catalan", R(X("m"),Minus,D(2))))))));
}
