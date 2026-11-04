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
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For n at least 14, arbitrary P,Q with nonempty union, and finite original families A subset WholeFiber P Q and B subset WholeFiber Q P whose opposite members share an ear, there are one common H subset E_K(P union Q) and families C,D on H. H consists of pairwise noncrossing actual ear chords. C,D are cross-intersecting and closed under every superset inside H.powerset. Their separate complete-fibre P|Q and Q|P masses dominate the respective original cardinalities. Each nonempty side stays nonempty; if both inputs are nonempty, a common output ear proves H nonempty. The empty initial E_K case is included: the same implication excludes two nonempty inputs. Apply the existing exists_terminal_compression to deletionSystem; terminal independence identifies feasible H with the entire powerset. This gives simultaneous terminal compression for the two original families. The source cases with cardinalities 2,3,4 and disjoint compatible P,Q are included; those extra assumptions are unnecessary here. Rank/count/Catalan bounds, strictness, total-count positivity, inclusion-exclusion Npq and the normalized bound remain outside this theorem. The construction makes no assertion that every independent trace has a triangulation completion, and no identification of the two weights."))), DescribeRole.Theorem),
            Paragraph(Text("Application to actual radial weights on the common terminal support. Fix n at least 14 with NeZero n, arbitrary finite P,Q of ZMod n with Disjoint P Q, Compatible(P union Q), and nonempty union. Let A be any finite subset of WholeFiber P Q and B any finite subset of WholeFiber Q P, with every T in A and U in B sharing an actual ear. Invoke exists_original_terminal_compression once and fix its single output H,C,D throughout. Its original premises require neither disjointness nor compatibility of P,Q; those are extra assumptions of this counting application. The original thirteen conclusions all remain attached to these same witnesses: support in E_K(P union Q), independence and pairwise noncrossing of H; both powerset inclusions, cross-intersection, both relative-upperness properties, both original-cardinality mass bounds, both one-sided nonemptiness implications, and nonemptiness of H when both inputs are nonempty. No input family is replaced by a saturated family.")),
            Paragraph(Text("For each X subset this H, consider the complete actual trace fibre ConditionFiber P Q H X. By the native ConditionFiber definition, its members are all original chord sets T satisfying IsTriangulation T, P subset EarCenters(T), Disjoint Q (EarCenters(T)), and EarCenters(T) intersect H = X. Keeping exactly the same T gives an equivalence with WholeFiber(P union X)(Q union(H minus X)); the inverse also keeps T. The trace equation forces X and forbids H minus X. Conversely, forcing X and forbidding H minus X makes the trace exactly X because X subset H. The same correspondence holds with P,Q interchanged:")),
            Paragraph(Math(Disp(All("X", Sets, Imp(SubF(X("X"),X("H")), Cj(
                C("Nonempty", C("Equiv", C("ConditionFiber",X("P"),X("Q"),X("H"),X("X")), Whole(Union(X("P"),X("X")),Union(X("Q"),C("sdiff",X("H"),X("X")))))),
                C("Nonempty", C("Equiv", C("ConditionFiber",X("Q"),X("P"),X("H"),X("X")), Whole(Union(X("Q"),X("X")),Union(X("P"),C("sdiff",X("H"),X("X")))))))))))),
            Paragraph(Text("This identity on triangulations preserves every completion and every ear outside H subject to the original P,Q restrictions. Distinct triangulations with the same trace stay distinct, so their full multiplicities are counted. The correspondence also preserves impossible or empty fibres, whose cardinalities are zero; it needs only X subset H, without geometric or realizability assumptions. In particular H empty and X empty give the original whole fibres, while X=H forces all of H and adds no forbidden centre from H. No representative, quotient, product decomposition, or completion choice is involved.")),
            Paragraph(Text("To apply PolygonConditionalCounts.conditional_card, the enlarged forced and forbidden sets must be disjoint and their union compatible. These conditions follow at the actual returned support: E_K(P union Q) excludes P union Q and makes each H ear noncrossing with every P or Q ear. Original compatibility handles pairs in P union Q, the terminal noncrossing conclusion handles pairs in H, and the E_K condition, with symmetry of crossing, handles mixed pairs. Thus P union X and Q union(H minus X) are disjoint and their union is the compatible set P union Q union H. Interchanging P,Q supplies the other orientation with the same H and X, rather than another placement.")),
            Paragraph(Text("Write p=card(P), q=card(Q), h=card(H), and for each X subset H write x=card(X). Disjointness gives card(P union X)=p+x and card(Q union(H minus X))=q+(h-x); here h-x is natural subtraction and x<=h. Apply conditional_card to those enlarged sets and transport Nat.card along the displayed identity on T. This gives the following exact integer counts for every X subset H; Npq is the native integer alternating Catalan sum, with its native natural index subtractions:")),
            Paragraph(Math(Disp(All("X", Sets, Imp(SubF(X("X"),X("H")), Cj(
                EqF(Seq(Open,Card(C("ConditionFiber",X("P"),X("Q"),X("H"),X("X"))),Colon,Sp,new Formula.Integers(),Close),
                    C("Npq",X("n"),AddF(X("p"),C("card",X("X"))),AddF(X("q"),Sub(X("h"),C("card",X("X")))))),
                EqF(Seq(Open,Card(C("ConditionFiber",X("Q"),X("P"),X("H"),X("X"))),Colon,Sp,new Formula.Integers(),Close),
                    C("Npq",X("n"),AddF(X("q"),C("card",X("X"))),AddF(X("p"),Sub(X("h"),C("card",X("X")))))))))))),
            Paragraph(Text("PolygonCompressionTrace.weight is the real cast of the complete trace-fibre Nat.card. Casting the two integer equalities to the reals therefore identifies the actual weights exactly. Realcast below denotes the cast into the reals, including the integer-to-real cast of Npq. No division, normalization, or positive-total hypothesis is used:")),
            Paragraph(Math(Disp(All("X", Sets, Imp(SubF(X("X"),X("H")), Cj(
                EqF(W(X("P"),X("Q"),X("H"),X("X")),Cast(C("Npq",X("n"),AddF(X("p"),C("card",X("X"))),AddF(X("q"),Sub(X("h"),C("card",X("X"))))))),
                EqF(W(X("Q"),X("P"),X("H"),X("X")),Cast(C("Npq",X("n"),AddF(X("q"),C("card",X("X"))),AddF(X("p"),Sub(X("h"),C("card",X("X"))))))))))))),
            Paragraph(Text("The native mass definition sums weights over a family. Every X in the fixed C or D is a subset of this H by the original powerset conclusions, so substitute the corresponding pointwise equality in each summand. The original separate mass bounds then become exact radial-sum bounds on the same C,D:")),
            Paragraph(Math(Disp(EqF(Mass(X("P"),X("Q"),X("H"),X("C")),
                Seq(Sum,Sp,Underscore,Grp(X("X"),InMacro,Sp,X("C")),Sp,
                    Cast(C("Npq",X("n"),AddF(X("p"),C("card",X("X"))),AddF(X("q"),Sub(X("h"),C("card",X("X"))))))))))),
            Paragraph(Math(Disp(EqF(Mass(X("Q"),X("P"),X("H"),X("D")),
                Seq(Sum,Sp,Underscore,Grp(X("X"),InMacro,Sp,X("D")),Sp,
                    Cast(C("Npq",X("n"),AddF(X("q"),C("card",X("X"))),AddF(X("p"),Sub(X("h"),C("card",X("X"))))))))))),
            Paragraph(Math(Disp(Le(Cast(C("card",X("A"))),
                Seq(Sum,Sp,Underscore,Grp(X("X"),InMacro,Sp,X("C")),Sp,
                    Cast(C("Npq",X("n"),AddF(X("p"),C("card",X("X"))),AddF(X("q"),Sub(X("h"),C("card",X("X"))))))))))),
            Paragraph(Math(Disp(Le(Cast(C("card",X("B"))),
                Seq(Sum,Sp,Underscore,Grp(X("X"),InMacro,Sp,X("D")),Sp,
                    Cast(C("Npq",X("n"),AddF(X("q"),C("card",X("X"))),AddF(X("p"),Sub(X("h"),C("card",X("X"))))))))))),
            Paragraph(Text("Radial here means that, for fixed P,Q,H, each weight depends on X through card(X). The two orientations retain their respective Npq arguments; this does not identify their weights, assert that C,D are determined by ranks, or turn either mass bound into equality for the original A,B. Empty C or D contributes the empty sum. Impossible trace fibres contribute zero with their full cardinal interpretation, without imposing positivity on H, A, B, C, D, any fibre, or any total.")),
            Paragraph(Text("The same enlarged compatible union has cardinality p+q+h, since P,Q,H are pairwise disjoint. PolygonEarContraction.compatible_card_bound applies because n>=14 implies n>=6, and gives the legal carrier bound on this actual H. Substitution of p=q=2 gives its two-by-two specialization:")),
            Paragraph(Math(Disp(Le(R(N(2),Cdot,AddF(AddF(X("p"),X("q")),X("h"))),X("n"))))),
            Paragraph(Math(Disp(Imps(Le(R(N(2),Cdot,AddF(X("h"),N(4))),X("n")),EqF(X("p"),N(2)),EqF(X("q"),N(2)))))),
            Paragraph(Text("These are unnormalized counts and bounds at the returned common support. Partition and normalization, an adjacent-ratio estimate for the actual Npq weights, actual cutoffs or an alternative completion route, same-F deficits, and the global all-n theorem remain unresolved. Neither positive total counts, the normalized inequality and its equality classification, nor a new completion or placement principle follows from this application."))
        ), []));
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
