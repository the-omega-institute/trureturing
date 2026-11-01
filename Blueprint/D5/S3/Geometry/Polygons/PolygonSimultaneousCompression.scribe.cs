using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons.PolygonSimultaneousCompressionFormula;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;

internal sealed class PolygonSimultaneousCompressionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common-support terminal compression of original polygon triangulation families",
        H("Common-support terminal compression of original polygon triangulation families"),
        Blocks(
            Describe.Lean(DescribeId.Create("polygonsimultaneouscompression-deletionsystem"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.deletionSystem"),
                H("deletionSystem"), StatementSource.FromAuthor(Disp(Sc(SetsAll(Imps(C("DeletionSystem",C("EK",Union(X("P"),X("Q")))) ,Lower(14),Nonempty(Union(X("P"),X("Q")))),"P","Q")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For n at least 14 and nonempty P union Q, this constructs the actual DeletionSystem on J=E_K(P union Q). At every H subset J its feasible universe is all independent subsets, its terminal predicate is Independent H, and its left/right weights are respectively weight P Q H and weight Q P H. Nonnegativity is cardinal nonnegativity. feasible_projection and marginal_weight realize all deletion fields. Properness and block_start choose a with a absent and a+1,a+2 present. The coordinates s=a+1,t=a+2,u=a+3 are distinct as required; local_excludes and shift_mem_feasible supply geometry. local_weight_law supplies the left law and, using union_comm on E_K, a separate right law. No weight equality is assumed. The displayed formula gives the constructor type; these field assignments specify its value."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polygonsimultaneouscompression-wholefiber"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.WholeFiber"),
                H("WholeFiber"), StatementSource.FromAuthor(Disp(Sc(SetsAll(EqF(Whole(X("P"),X("Q")),C("ConditionFiber",X("P"),X("Q"),C("empty"),C("empty"))),"P","Q")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("WholeFiber P Q is the subtype of all actual triangulations forcing P and forbidding Q, with the vacuous exact trace on the empty observation support. Families are arbitrary finite subsets of this subtype."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polygonsimultaneouscompression-familytraces"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.familyTraces"),
                H("familyTraces"), StatementSource.FromAuthor(Disp(Sc(SetsAll(All("A",C("Finset",Whole(X("P"),X("Q"))),All("X",Sets,IffF(InF(X("X"),Traces(X("H"),X("A"))),ExistsF("T",Whole(X("P"),X("Q")),Cj(InF(X("T"),X("A")),EqF(X("X"),Inter(Ears(C("val",X("T"))),X("H")))))))),"P","Q","H")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The image contains precisely the observed ear traces of selected original members. It does not replace a partial fibre by a full fibre at the level of the original family."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polygonsimultaneouscompression-familytraces-feasible"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.familyTraces_feasible"),
                H("familyTraces feasible"), StatementSource.FromAuthor(Disp(Sc(SetsAll(All("A",C("Finset",Whole(X("P"),X("Q"))),Imp(Lower(6),SubF(Traces(X("H"),X("A")),Omega(X("H"))))),"P","Q","H")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every image trace is feasible because each original member is an actual triangulation. Feasible traces without completions remain in the universe."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygonsimultaneouscompression-original-card-le-trace-mass"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.original_card_le_trace_mass"),
                H("original card le trace mass"), StatementSource.FromAuthor(Disp(Sc(SetsAll(All("A",C("Finset",Whole(X("P"),X("Q"))),Le(Cast(C("card",X("A"))),Mass(X("P"),X("Q"),X("H"),Traces(X("H"),X("A"))))),"P","Q","H")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Finset.card_eq_sum_card_image counts original members fibre by fibre. Each selected fibre injects, by retaining its original triangulation, into the complete ConditionFiber P Q H X. Summing the cardinal bounds gives an inequality. No saturation equality is asserted, and no global positivity or explicit conditional-count formula is needed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygonsimultaneouscompression-shared-ear-mem-ek"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.shared_ear_mem_EK"),
                H("shared ear mem EK"), StatementSource.FromAuthor(Disp(Sc(SetsAll(All("T",Whole(X("P"),X("Q")),All("U",Whole(X("Q"),X("P")),All("i",Vertex,Imps(InF(X("i"),C("EK",Union(X("P"),X("Q")))),InF(X("i"),Ears(C("val",X("T")))),InF(X("i"),Ears(C("val",X("U")))))))),"P","Q")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A common ear cannot lie in P or Q, since the opposite member forbids that side. For every k in P use noncrossing in the first triangulation, and for k in Q use the second. Thus the common ear avoids all K ears and belongs to the full allowed E_K K."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygonsimultaneouscompression-common-ears-eq-trace-inter"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.common_ears_eq_trace_inter"),
                H("common ears eq trace inter"), StatementSource.FromAuthor(Disp(Sc(SetsAll(All("T",Whole(X("P"),X("Q")),All("U",Whole(X("Q"),X("P")),EqF(Inter(Ears(C("val",X("T"))),Ears(C("val",X("U")))),Inter(Inter(Ears(C("val",X("T"))),C("EK",Union(X("P"),X("Q")))),Inter(Ears(C("val",X("U"))),C("EK",Union(X("P"),X("Q")))))))),"P","Q")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("This is the full-ear to trace-intersection bridge (source 37.5). It uses the complete E_K(P union Q), rather than a protected subcarrier chosen in advance."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygonsimultaneouscompression-familytraces-cross"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.familyTraces_cross"),
                H("familyTraces cross"), StatementSource.FromAuthor(Disp(Sc(SetsAll(FamilyAll(Imp(OriginalCross,C("CrossIntersecting",Traces(C("EK",Union(X("P"),X("Q"))),X("A")),Traces(C("EK",Union(X("P"),X("Q"))),X("B"))))),"P","Q")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Full-ear cross-intersection of opposite original members descends to cross-intersection of their allowed traces, by the exact intersection bridge."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygonsimultaneouscompression-exists-original-terminal-compression"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.exists_original_terminal_compression"),
                H("exists original terminal compression"), StatementSource.FromAuthor(Disp(Sc(SetsAll(FamilyAll(Imps(ExistsF("H",Sets,ExistsF("C",Family,ExistsF("D",Family,Cj(
                SubF(X("H"),C("EK",Union(X("P"),X("Q")))),Ind(X("H")),Geometric(X("H")),
                SubF(X("C"),Powers(X("H"))),SubF(X("D"),Powers(X("H"))),C("CrossIntersecting",X("C"),X("D")),
                C("RelativelyUpper",Powers(X("H")),X("C")),C("RelativelyUpper",Powers(X("H")),X("D")),
                Le(Cast(C("card",X("A"))),Mass(X("P"),X("Q"),X("H"),X("C"))),
                Le(Cast(C("card",X("B"))),Mass(X("Q"),X("P"),X("H"),X("D"))),
                Imp(Nonempty(X("A")),Nonempty(X("C"))),Imp(Nonempty(X("B")),Nonempty(X("D"))),
                Imps(Nonempty(X("H")),Nonempty(X("A")),Nonempty(X("B"))))))),Lower(14),Nonempty(Union(X("P"),X("Q"))),OriginalCross)),"P","Q")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For n at least 14, arbitrary P,Q with nonempty union, and finite original families A subset WholeFiber P Q and B subset WholeFiber Q P whose opposite members share an ear, there are one common H subset E_K(P union Q) and families C,D on H. H consists of pairwise noncrossing actual ear chords. C,D are cross-intersecting and closed under every superset inside H.powerset. Their separate complete-fibre P|Q and Q|P masses dominate the respective original cardinalities. Each nonempty side stays nonempty; if both inputs are nonempty, a common output ear proves H nonempty. The empty initial E_K case is included: the same implication excludes two nonempty inputs. Apply the existing exists_terminal_compression to deletionSystem; terminal independence identifies feasible H with the entire powerset. This realizes exactly the compression prefix of B-37.2 residual child 82a336ea36dcb1fdf33de82be432b2ef57a5cccb4770e8737a97a557029cda16, bytes [0,1646), parent bb66dfd880da1b1f58a57a9d778dd6406ce5738d2f047f6862da8c62cf8288f6 bytes [4005,5651). The source cases with cardinalities 2,3,4 and disjoint compatible P,Q are included; those extra assumptions are unnecessary here. Rank/count/Catalan bounds, strictness, total-count positivity, inclusion-exclusion Npq and the normalized bound remain outside this theorem. The construction makes no assertion that every independent trace has a triangulation completion, and no identification of the two weights."))), DescribeRole.Theorem)), []));
}

internal static class PolygonSimultaneousCompressionFormula
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
