using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons.PolygonEarSlideCardinalityFormula;
using static StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons.PolygonCompressionFormula;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;

internal sealed class PolygonCompressionTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual cyclic geometry, independent trace universes and complete-fibre deletion",
        H("Actual cyclic geometry, independent trace universes and complete-fibre deletion"),
        Blocks(
            Describe.Lean(DescribeId.Create("polygoncompressiontrace-independent"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCompressionTrace.Independent"),
                H("Independent"), StatementSource.FromAuthor(Disp(Sc(All("H",Sets,IffF(Ind(X("H")),All("i",Vertex,Imp(InF(X("i"),X("H")),Not(InF(AddF(X("i"),N(1)),X("H"))))))),false))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Independent means no adjacent cyclic centres, including across the cyclic boundary."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polygoncompressiontrace-feasible"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCompressionTrace.feasible"),
                H("feasible"), StatementSource.FromAuthor(Disp(Sc(SetsAll(IffF(InF(X("X"),Omega(X("H"))),Cj(SubF(X("X"),X("H")),Ind(X("X")))),"H","X"),false))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The universe contains every independent subset of H. It includes impossible traces; no completion is selected or required."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polygoncompressiontrace-weight"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCompressionTrace.weight"),
                H("weight"), StatementSource.FromAuthor(Disp(Sc(SetsAll(EqF(W(X("P"),X("Q"),X("H"),X("X")),Cast(Card(Fibre(X("H"),X("X"))))),"P","Q","H","X")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The real weight is Nat.card of the entire ConditionFiber P Q H X subtype: every finite maximal noncrossing diagonal carrier with P forced, Q forbidden and exact ear trace X on H. All chords outside H are retained."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polygoncompressiontrace-mem-feasible"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCompressionTrace.mem_feasible"),
                H("mem feasible"), StatementSource.FromAuthor(Disp(Sc(SetsAll(IffF(InF(X("X"),Omega(X("H"))),Cj(SubF(X("X"),X("H")),Ind(X("X")))),"H","X"),false))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Membership exposes both the support and cyclic independence requirements."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygoncompressiontrace-independent-subset"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCompressionTrace.independent_subset"),
                H("independent subset"), StatementSource.FromAuthor(Disp(Sc(SetsAll(Imps(Ind(X("X")),Ind(X("H")),SubF(X("X"),X("H"))),"H","X"),false))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Cyclic independence passes to subsets, and is used for actual traces and deletion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygoncompressiontrace-cross-ear-iff-adjacent"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCompressionTrace.cross_ear_iff_adjacent"),
                H("cross ear iff adjacent"), StatementSource.FromAuthor(Disp(Sc(All("i",Vertex,All("j",Vertex,Imp(Lower(6),IffF(Cross(X("i"),X("j")),R(EqF(X("j"),AddF(X("i"),N(1))),Lor,EqF(X("i"),AddF(X("j"),N(1))))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For n at least 6 the actual strict cyclic crossing of ear chords occurs exactly at adjacent centres. Translate i to 1, apply the existing crossing endpoint lemma, then use symmetric-pair endpoint equality; the converse is transported from local_crossings. No abstract replacement of the geometric crossing relation is made."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygoncompressiontrace-earcenters-independent"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCompressionTrace.earCenters_independent"),
                H("earCenters independent"), StatementSource.FromAuthor(Disp(Sc(All("T",Chords,Imps(Ind(Ears(X("T"))),Lower(6),Tri(X("T"))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every actual triangulation has an independent set of ear centres, by noncrossing of its chord carrier."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygoncompressiontrace-block-start"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCompressionTrace.block_start"),
                H("block start"), StatementSource.FromAuthor(Disp(Sc(All("H",Sets,Imps(ExistsF("a",Vertex,Cj(Not(InF(X("a"),X("H"))),InF(Pos(true,1),X("H")),InF(Pos(true,2),X("H")))),Ne(X("H"),C("univ")),ExistsF("b",Vertex,Cj(InF(X("b"),X("H")),InF(AddF(X("b"),N(1)),X("H"))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every proper support containing an adjacent pair has a cyclic block start a absent from H with a+1,a+2 present. If none existed, predecessors of each adjacent pair would be present. Induction gives b-k,b+1-k in H for all natural k, and k=(b-z).val reaches any z, contradicting properness. This lemma needs only NeZero n."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygoncompressiontrace-trace-mem-feasible"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCompressionTrace.trace_mem_feasible"),
                H("trace mem feasible"), StatementSource.FromAuthor(Disp(Sc(All("T",Chords,All("H",Sets,Imps(InF(Inter(Ears(X("T")),X("H")),Omega(X("H"))),Lower(6),Tri(X("T")))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The exact ear trace of each actual triangulation belongs to the full independent-subset universe."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygoncompressiontrace-weight-zero-of-not-feasible"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCompressionTrace.weight_zero_of_not_feasible"),
                H("weight zero of not feasible"), StatementSource.FromAuthor(Disp(Sc(SetsAll(Imps(EqF(W(X("P"),X("Q"),X("H"),X("X")),N(0)),Lower(6),Not(InF(X("X"),Omega(X("H"))))),"P","Q","H","X")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A trace outside the feasible universe has empty actual fibre, hence zero raw weight. This removes infeasible extension terms without asserting realizability of feasible traces."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygoncompressiontrace-feasible-projection"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCompressionTrace.feasible_projection"),
                H("feasible projection"), StatementSource.FromAuthor(Disp(Sc(All("H",Sets,All("t",Vertex,EqF(C("imageErase",Omega(X("H")),X("t")),Omega(Erase(X("H"),X("t")))))),false))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Deleting t maps the full feasible trace family exactly onto the family on H minus t. In reverse, R itself is a preimage; insertion of t need not be feasible."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygoncompressiontrace-condition-fibre-card-delete"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCompressionTrace.condition_fibre_card_delete"),
                H("condition fibre card delete"), StatementSource.FromAuthor(Disp(Sc(SetsAll(All("t",Vertex,Imps(EqF(Card(Fibre(Erase(X("H"),X("t")),X("R"))),AddF(Card(Fibre(X("H"),X("R"))),Card(Fibre(X("H"),Insert(X("t"),X("R")))))),InF(X("t"),X("H")),Not(InF(X("t"),X("R"))))),"P","Q","H","R")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The entire reduced observation fibre is partitioned by whether t is an ear. Both equivalences retain the same original chord set and all forced/forbidden conditions. This is an equality of raw cardinalities, with no lower bound on n and no nonempty-completion premise."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygoncompressiontrace-marginal-weight"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCompressionTrace.marginal_weight"),
                H("marginal weight"), StatementSource.FromAuthor(Disp(Sc(SetsAll(All("t",Vertex,Imps(EqF(C("marginalWeight",Omega(X("H")),C("weight",X("P"),X("Q"),X("H")),X("t"),X("R")),W(X("P"),X("Q"),Erase(X("H"),X("t")),X("R"))),Lower(6),InF(X("t"),X("H")),InF(X("R"),Omega(Erase(X("H"),X("t")))))),"P","Q","H","R")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The finite projection fibre consists of R and insert(t,R) when the latter is feasible. The complete-cardinality partition and zero weight of infeasible traces identify its sum with the actual reduced weight. This law is applied separately to P|Q and Q|P."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygoncompressiontrace-proper-of-subset-ek"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCompressionTrace.proper_of_subset_EK"),
                H("proper of subset EK"), StatementSource.FromAuthor(Disp(Sc(SetsAll(Imps(Ne(X("H"),C("univ")),Nonempty(X("K")),SubF(X("H"),C("EK",X("K")))),"K","H")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Any member k of nonempty K is excluded from E_K K, so every support contained in E_K K is proper."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygoncompressiontrace-feasible-of-independent"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCompressionTrace.feasible_of_independent"),
                H("feasible of independent"), StatementSource.FromAuthor(Disp(Sc(All("H",Sets,Imp(Ind(X("H")),EqF(Omega(X("H")),Powers(X("H"))))),false))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("At a terminal independent support, every subset is feasible; zero actual weights may still occur."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygoncompressiontrace-shift-mem-feasible"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCompressionTrace.shift_mem_feasible"),
                H("shift mem feasible"), StatementSource.FromAuthor(Disp(Sc(All("a",Vertex,SetsAll(Imps(InF(Shift(X("a"),X("X")),Omega(X("H"))),Not(InF(X("a"),X("H"))),InF(Pos(true,1),X("H")),InF(X("X"),Omega(X("H")))),"H","X")),false))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("At a block start, replacing a+2 by a+1 stays feasible. A newly adjacent predecessor would have to be a, which is absent from H; the successor a+2 was deleted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygoncompressiontrace-local-excludes"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCompressionTrace.local_excludes"),
                H("local excludes"), StatementSource.FromAuthor(Disp(Sc(All("a",Vertex,SetsAll(Imps(Cj(Not(InF(Pos(true,1),X("X"))),Not(InF(Pos(true,3),X("X")))),InF(X("X"),Omega(X("H"))),InF(Pos(true,2),X("X"))),"H","X")),false))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A feasible trace containing a+2 omits both adjacent centres a+1 and a+3."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygoncompressiontrace-local-weight-law"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCompressionTrace.local_weight_law"),
                H("local weight law"), StatementSource.FromAuthor(Disp(Sc(All("a",Vertex,SetsAll(Imps(EqF(W(X("P"),X("Q"),X("H"),X("X")),AddF(W(X("P"),X("Q"),X("H"),Shift(X("a"),X("X"))),C("ite",InF(Insert(Pos(true,3),Shift(X("a"),X("X"))),Omega(X("H"))),W(X("P"),X("Q"),X("H"),Insert(Pos(true,3),Shift(X("a"),X("X")))),N(0)))),Lower(14),SubF(X("H"),C("EK",Union(X("P"),X("Q")))),Not(InF(X("a"),X("H"))),InF(Pos(true,1),X("H")),InF(Pos(true,2),X("H")),InF(X("X"),Omega(X("H"))),InF(Pos(true,2),X("X"))),"P","Q","H","X"))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Use the merged condition_fibre_card_at with R=X minus a+2. The local exclusions give its required support. Its optional branch tests a+3 in H, whereas generic compression tests feasibility of the extended trace. If the extension is infeasible its complete fibre is empty, including when a+4 is already present. If a+3 is outside H the extension is outside H as well. Thus the two tests give the same weighted equation for all traces, including impossible ones."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygoncompressiontrace-independent-iff-noncrossing"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCompressionTrace.independent_iff_noncrossing"),
                H("independent iff noncrossing"), StatementSource.FromAuthor(Disp(Sc(All("H",Sets,Imp(Lower(6),IffF(Ind(X("H")),Geometric(X("H")))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The terminal predicate is exactly pairwise noncrossing of actual ear chords, not a completion-existence criterion."))), DescribeRole.Theorem)), []));
}

internal static class PolygonCompressionFormula
{
    internal static Formula Family => C("Finset", Sets);
    internal static Formula Omega(Formula h) => C("feasible", h);
    internal static Formula Ind(Formula h) => C("Independent", h);
    internal static Formula W(Formula p, Formula q, Formula h, Formula x) => C("weight", p, q, h, x);
    internal static Formula Card(Formula f) => C("Natcard", f);
    internal static Formula Cast(Formula f) => C("Realcast", f);
    internal static Formula Ne(Formula x, Formula y) => Not(EqF(x,y));
    internal static Formula Le(Formula x, Formula y) => R(x, Leq, y);
    internal static Formula Nonempty(Formula x) => C("Nonempty", x);
    internal static Formula Powers(Formula h) => C("powerset", h);
    internal static Formula Shift(Formula a, Formula x) => C("shift", AddF(a,N(1)), AddF(a,N(2)), x);
    internal static Formula Cj(params Formula[] fs) { Formula r = fs[^1]; for(int i=fs.Length-2;i>=0;i--) r=AndF(fs[i],r); return r; }
    internal static Formula Imps(Formula result, params Formula[] hs) { for(int i=hs.Length-1;i>=0;i--) result=Imp(hs[i],result); return result; }
    internal static Formula Sc(Formula f, bool nz=true) => nz ? Scope(f) : All("n", X("Nat"), f);
    internal static Formula Cross(Formula i, Formula j) => C("Cross", C("ear",i),C("ear",j));
    internal static Formula Geometric(Formula h) => All("i",Vertex,Imp(InF(X("i"),h),All("j",Vertex,Imp(InF(X("j"),h),Not(Cross(X("i"),X("j")))))));
    internal static Formula Whole(Formula p,Formula q) => C("WholeFiber",p,q);
    internal static Formula Traces(Formula h,Formula a) => C("familyTraces",h,a);
    internal static Formula Mass(Formula p,Formula q,Formula h,Formula a) => C("mass",C("weight",p,q,h),a);
    internal static Formula FamilyAll(Formula body) => All("A",C("Finset",Whole(X("P"),X("Q"))),All("B",C("Finset",Whole(X("Q"),X("P"))),body));
    internal static Formula OriginalCross => All("T",Whole(X("P"),X("Q")),Imp(InF(X("T"),X("A")),All("U",Whole(X("Q"),X("P")),Imp(InF(X("U"),X("B")),Not(C("Disjoint",Ears(C("val",X("T"))),Ears(C("val",X("U")))))))));
}
