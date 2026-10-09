using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SparseThickFrameFamilyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.";
    private static Formula I(string s) => F.Id(s);
    private static Formula N => Seq(Mathbb, Grp(I("N")));
    private static Formula Z => Seq(Mathbb, Grp(I("Z")));
    private static Formula Call(string s, params Formula[] a) =>
        new Formula.Apply(Seq(Operatorname, Grp(I(s))), [.. a]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(string s, Formula t, Formula b) =>
        Seq(Forall, Sp, I(s), Sp, InMacro, Sp, t, Comma, Sp, b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Par(a), b);
    private static Formula And(params Formula[] a)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (var x in a)
        {
            if (parts.Count > 0) parts.AddRange([Sp, Land, Sp]);
            parts.Add(Par(x));
        }
        return Seq([.. parts]);
    }
    private static Formula U => Call("min", I("u"), I("k"));
    private static Formula V => Call("min", I("v"), I("k"));
    private static Formula Side => Call("side", I("k"));
    private static Formula Index => Call("FrameIndex", I("k"), U, V);
    private static Formula Word => Call("sourceWord", I("u"), I("v"), I("k"), U, V, I("x"));
    private static Formula Rows => Call("sourceRows", I("k"), U, V, I("x"));
    private static Formula L => Call("grid", U, Side, Call("fst", I("x")));
    private static Formula Height => Call("grid", V, Side, Call("fst", Call("snd", I("x"))));
    private static Formula P => Call("squareRows", Rows);
    private static Formula R => Call("oddRows", Rows);
    private static Formula BaseP => Mul(Call("thickness", I("k"), U), Pow(L, D(2)));
    private static Formula BaseR => Mul(Call("thickness", I("k"), V), Pow(Height, D(2)));
    private static Formula Band => Mul(Mul(D(7), I("k")), Side);
    private static Formula Q => Call("q", Call("level", I("k")));
    private static Formula CountU => Call("gridCount", U, Side);
    private static Formula CountV => Call("gridCount", V, Side);
    private static Formula Size => Mul(Mul(CountU, CountV), Pow(Q, D(6)));
    private static Formula Joint => Call("Pair", Call("e", Call("G", Word)), Call("f", Call("G", Word)));
    private static Formula Fun(Formula b) => Call("fun", Seq(I("x"), Colon, Index), b);
    private static Formula Inj(Formula b) => Call("Injective", Fun(b));
    private static Formula Card(Formula b) => Call("ncard", Call("range", Fun(b)));

    private static Formula FamilyFormula()
    {
        var perWord = All("x", Index, And(
            Seq(Word, Sp, InMacro, Sp, Call("wordFiber", I("u"), I("v"), I("k"))),
            Eqn(Call("count", Word, I("true")), I("u")),
            Eqn(Call("count", Word, I("false")), I("v")),
            Eqn(Call("scatteredTrueFalseCount", Word), I("k")),
            Eqn(Call("rows", Word), Call("append", Rows,
                Call("replicate", Sub(I("v"), Call("length", Rows)), D(0)))),
            Eqn(Call("length", Rows), Height), Call("SortedGE", Rows),
            All("a", Rows, Le(I("a"), L)), Eqn(Call("sum", Rows), I("k")),
            Le(BaseP, P), Le(P, Add(BaseP, Band)), Le(BaseR, R), Le(R, Add(BaseR, Band))));
        var result = And(perWord, Inj(Call("Pair", P, R)), Inj(Joint), Inj(Word),
            Eqn(Card(Word), Size), Eqn(Card(Joint), Size),
            Le(Size, Call("capacity", I("u"), I("v"), I("k"))),
            Le(U, Mul(Mul(D(6, 1, 4, 4), Side), CountU)),
            Le(V, Mul(Mul(D(6, 1, 4, 4), Side), CountV)),
            Lt(Side, Mul(D(1, 1, 2, 0), Q)), Le(I("k"), Pow(Side, D(2))),
            Le(Mul(Mul(Mul(Call("c0"), U), V), Pow(I("k"), D(2))),
                Call("capacity", I("u"), I("v"), I("k"))));
        return All("u", N, All("v", N, All("k", N,
            Seq(And(Le(D(4, 0, 9, 6), I("k")),
                Le(Mul(D(4, 0, 9, 6), I("k")), Pow(I("u"), D(2))),
                Le(Mul(D(4, 0, 9, 6), I("k")), Pow(I("v"), D(2)))), Sp, Implies, Sp, result))));
    }

    private static Formula FullFormula()
    {
        var k = Call("min", I("K"), Sub(Mul(I("u"), I("v")), I("K")));
        var u = Call("min", I("u"), k);
        var v = Call("min", I("v"), k);
        var word = Call("originalWord", I("u"), I("v"), I("K"), I("x"));
        var index = Call("OriginalIndex", I("u"), I("v"), I("K"));
        var joint = Call("Pair", Call("e", Call("G", word)), Call("f", Call("G", word)));
        Formula fun(Formula a) => Call("fun", Seq(I("x"), Colon, index), a);
        Formula card(Formula a) => Call("ncard", Call("range", fun(a)));
        var capacity = Call("capacity", I("u"), I("v"), I("K"));
        var size = Call("originalFamilySize", I("u"), I("v"), I("K"));
        var family = Seq(Le(D(4, 0, 9, 6), k), Sp, Implies, Sp, And(
            All("x", index, Seq(word, Sp, InMacro, Sp,
                Call("wordFiber", I("u"), I("v"), I("K")))),
            Call("Injective", fun(joint)), Call("Injective", fun(word)),
            Eqn(card(word), size), Eqn(card(joint), size)));
        var hypotheses = And(Le(D(1), I("u")), Le(D(1), I("v")), Le(D(0), I("K")),
            Le(I("K"), Mul(I("u"), I("v"))), Le(D(1), k),
            Le(Mul(D(4, 0, 9, 6), k), Pow(Call("min", I("u"), I("v")), D(2))));
        return All("u", Z, All("v", Z, All("K", Z, Seq(hypotheses, Sp, Implies, Sp,
            And(Le(Mul(Mul(Mul(Call("c0"), u), v), Pow(k, D(2))), capacity),
                Le(capacity, Mul(Mul(u, v), Pow(k, D(2)))), family)))));
    }

    private static DocumentBlock Def(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact-area thick frames, separated width and height grids, and an actual common word family.",
        H("Separated thick-frame word family"), Blocks(
            Def("ceil-square-side", "side", "The ceiling square side",
                "side(k)=Nat.sqrt(k−1)+1. For positive k this is the ceiling of the square root, including perfect squares."),
            Def("frame-thickness", "thickness", "Variable frame thickness",
                "thickness(k,U)=(k+U−1)/U in natural division. For positive U this is the ceiling of k/U."),
            Def("grid-size", "gridCount", "Exact grid size",
                "gridCount(U,h)=(floor(U/6)−floor((U+7)/8))/(128h)+1. For U≥4096 and h>0 the natural subtraction does not truncate."),
            Def("grid-point", "grid", "Width and height grid points",
                "grid(U,h,i)=floor((U+7)/8)+128h i for every i in Fin(gridCount(U,h)). For U≥4096 and h>0 all points lie between ceil(U/8) and floor(U/6), and successive points differ by 128h."),
            Def("core-level", "level", "The maximal dyadic core level",
                "level(k)=Nat.log2(1+side(k)/560). Its radix q=2^level(k) satisfies 8 coreSide(level(k))≤side(k) and side(k)<1120q."),
            Def("frame-residual-area", "residualArea", "The exact residual area",
                "For r=thickness(k,U) and s=thickness(k,V), residualArea(k,U,V,L,H)=k−(rL+sH)+rs. Under the large-area sparse hypotheses, both grids satisfy rL+sH≤k before the natural subtraction is used, and h²≤8t≤7h²."),
            Def("thick-frame-rows", "frameRows", "Rows of one thick frame",
                "frameRows(r,s,L,H,h,mu) consists of r copies of L, the h actual rows of mu translated by s, and H−r−h copies of s. If mu is sorted, has length h and has every row at most h, then L≥s+h and H≥r+h make this a sorted Ferrers partition of height H. Both statistics refer to this same partition."),
            Def("full-frame-index", "FrameIndex", "The full independent index domain",
                "FrameIndex(k,U,V)=Fin(gridCount(U,side(k))) × Fin(gridCount(V,side(k))) × CoreIndex(level(k)). All width, height and both radix-eight coordinates are retained."),
            Def("actual-source-rows", "sourceRows", "The actual framed square rows",
                "Under the large-area sparse hypotheses, choose L,H from the two indices, set t=residualArea(k,U,V,L,H), and apply the existing W(level(k),side(k),t,x) square-word construction. Its direct rows, without changing t or reversing the square core, are inserted in frameRows."),
            Def("actual-source-word", "sourceWord", "The word in the original dimensions",
                "Under the large-area sparse hypotheses with U=min(u,k) and V=min(v,k), append zero rows until there are v rows and apply wordOfRows with width u. The result has exactly u true letters, v false letters and scattered true-false area k."),
            Def("absolute-capacity-constant", "c0", "The absolute constant",
                "c0=1/(6144² 1120⁶), independent of every dimension, area and aspect ratio."),
            Describe.Lean(DescribeId.Create("separated-global-family"),
                DeclarationHandle.Create(Prefix + "separated_frame_family"),
                H("An actual globally separated joint family"), StatementSource.FromAuthor(Disp(FamilyFormula())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Put U=min(u,k), V=min(v,k) and h=side(k). The sparse hypotheses derive U,V≥4096, U,V≥32h, 1≤r,s≤h, k≤rU,sV≤2k, and 1024rs≤k. Every grid frame fits, and its exact residual area satisfies the existing square_family hypotheses. No core existence or grid cardinality is assumed.")),
                    Paragraph(Text("For mu=rows(W), the two frame formulas are P=rL²+(H−r)s²+2st+squareRows(mu) and R=sH²+(L−s)r²+2rt+oddRows(mu). The direct row recursion gives 0≤squareRows(mu)≤ht and 0≤oddRows(mu)≤2ht. Consequently the first correction is at most 5kh and the second at most 6kh, so both lie in the displayed bands of width 7kh. The identity same_diagram_columns identifies oddRows with the squared column heights of the same actual diagram.")),
                    Paragraph(Text("If two widths differ, spacing 128h and rU≥k make their first bands disjoint; differing heights make the second bands disjoint. Equality of the joint statistics therefore recovers both grid indices. The frame formulas then recover the two square-core statistics, and square_family recovers the core index. Zero padding preserves both statistics. The direct_list_fan affine formulas convert their joint injection into joint signed fan injection for the actual wordOfRows words.")),
                    Paragraph(Text("The word and joint fan images each have exactly gridCount(U,h) gridCount(V,h) q^6 members, and this is a lower bound for the whole fixed-area word-fiber capacity. The grid counts satisfy U≤6144h gridCount(U,h) and V≤6144h gridCount(V,h), while h<1120q and k≤h². Multiplying these bounds gives c0 UVk²≤gridCount(U,h) gridCount(V,h) q^6≤capacity(u,v,k), with exactly c0=1/(6144² 1120⁶). This theorem concerns the large-area branch with actual area k."))),
                DescribeRole.Theorem),
            Def("normalized-integer-area", "normalizedArea", "The normalized integer area",
                "normalizedArea(u,v,K)=toNat(min(K,uv−K)). The positive-area hypotheses establish nonnegativity before this conversion is used."),
            Def("original-integer-index", "OriginalIndex", "Indices in the original integer parameters",
                "OriginalIndex(u,v,K) is FrameIndex at normalizedArea and at the two minimum natural dimensions. Under the integer guards these dimensions equal U=min(u,k) and V=min(v,k)."),
            Def("original-integer-word", "originalWord", "The explicit word at the original area",
                "Construct sourceWord at the original natural dimensions and normalized area. If K equals that area, keep this word; otherwise reverse its letters. Under the full integer hypotheses, outer_reverse_contract proves that the latter word has area uv−k=K and preserves its joint signed moments."),
            Def("original-family-size", "originalFamilySize", "The exact original family size",
                "At k=normalizedArea(u,v,K), originalFamilySize is gridCount(min(toNat(u),k),side(k)) times gridCount(min(toNat(v),k),side(k)) times q(level(k))^6. Each factor comes from the full computed index domain."),
            Describe.Lean(DescribeId.Create("full-sparse-capacity"),
                DeclarationHandle.Create(Prefix + "sparse_joint_moment_capacity"),
                H("Sparse capacity in the complete integer domain"),
                StatementSource.FromAuthor(Disp(FullFormula())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every positive integer u,v and every integer 0≤K≤uv, put k=min(K,uv−K), U=min(u,k), V=min(v,k). If k≥1 and 4096k≤min(u,v)², the capacity of the whole actual word fiber lies between c0 UVk² and UVk². Both original areas, every aspect ratio, perfect-square k and the full small positive range remain included.")),
                    Paragraph(Text("For an actual word of area k, its sorted direct rows and the transpose of the same diagram have natural square sums. Both are at least k. Each row is bounded by U, so the first sum is at most Uk. For the same actual diagram, diagram_col_bound bounds each column height by v, and a double incidence count proves that the column heights sum to k. Each is therefore also at most k. Using same_diagram_columns and the transpose row lengths bounds the second sum by Vk. These two integer statistics from the same word belong to the joint rectangle [1,Uk] × [1,Vk]. The actual fan map sends this rectangle to an ambient set of at most UVk² points. Counting the ambient product proves an upper bound and does not assert simultaneous attainment of independently optimized marginals.")),
                    Paragraph(Text("When 1≤k<4096, the sparse guard implies u,v≥k. The concrete sorted rows consist of one row k and v−1 zero rows. wordOfRows gives a nonempty actual word with the required counts and area, so the whole joint image has at least one point. The unchanged constant satisfies c0 UVk²≤c0 k⁴≤c0 4096⁴≤1. This directly constructs the small-area branch.")),
                    Paragraph(Text("For k≥4096 the actual thick-frame family above gives the lower bound. Integer nonnegativity proves every toNat cast faithful. The existing joint_image_reverse equates the whole capacities at k and uv−k. Applying outer_reverse_contract to every constructed mathematical word preserves its joint moment pair and produces the original K. Thus originalWord has exactly the original u,v counts and area K, its joint map is injective, and its word and joint images each have exactly originalFamilySize members. These are source words, not claims about a physically free reversal operation or recovery of an arbitrary parenthesized tree."))),
                DescribeRole.Theorem))));
}
