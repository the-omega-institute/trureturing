using System.Linq;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases.MazorchukXuReconstructionNotation;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

internal static class MazorchukXuReconstructionNotation
{
    internal static Formula N => Fn("Nat");
    internal static Formula Q => Fn("Rat");
    internal static Formula Prop => Fn("Prop");
    internal static Formula Ty => Fn("Type");
    internal static Formula Pairs => Fn("Prod", N, N);
    internal static Formula Points => Fn("Finset", Pairs);
    internal static Formula V(string name) => F.Id(name);
    internal static Formula Fn(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    internal static Formula Apply(Formula fn, params Formula[] args) =>
        Seq(fn, Open, new Formula.LatexSequence([.. args.SelectMany((a, i) =>
            i == 0 ? new[] { a } : new[] { Comma, Sp, a })]), Close);
    internal static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    internal static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    internal static Formula Many(string names, Formula domain, Formula body)
    {
        foreach (var name in names.Split(' ').Reverse()) body = All(name, domain, body);
        return body;
    }
    internal static Formula Par(Formula a) => Seq(Open, a, Close);
    internal static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Par(a), op, Par(b));
    internal static Formula And(params Formula[] xs) =>
        xs.Aggregate((a, b) => Logic(a, FormulaLogicOperator.And, b));
    internal static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    internal static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    internal static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    internal static Formula Not(Formula a) => Seq(Neg, Sp, Par(a));
    internal static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    internal static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    internal static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    internal static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    internal static Formula Subset(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    internal static Formula Plus(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    internal static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    internal static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    internal static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    internal static Formula Set(string name, Formula domain, Formula predicate) =>
        Seq(OpenBrace, V(name), Sp, InMacro, Sp, domain, Bar, Sp, predicate, CloseBrace);
    internal static Formula Rel(Formula a) => new Formula.TypeArrow(a, new Formula.TypeArrow(a, Prop));
    internal static Formula Map(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    internal static Formula Ordered(string name, Formula body) =>
        All(name, Ty, Seq(OpenBracket, Fn("LinearOrder", V(name)), CloseBracket, Sp, body));
    internal static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/mazorchukxu2026cokernel");
    internal static DocumentBlock Node(string module, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature = false) =>
        Describe.Lean(DescribeId.Create("mazorchuk-xu-" + module.ToLowerInvariant() + "-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Combinatorics/BinomialBases/MazorchukXu" + module + "." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}


internal sealed class MazorchukXuReconstructionDocument : IScribeDocumentDefinition
{
    private static Formula I => V("i");
    private static Formula M => V("M");
    private static Formula FinI => Fn("Fin",I);
    private static Formula List => Map(FinI,N);
    private static Formula P => V("p");
    private static Formula C => V("c");
    private static Formula B => V("B");
    private static Formula T => Fn("BoundedCoordinateVertex",M,P);
    private static Formula A => Fn("coordinateEdgeSet",M,P,C,B);
    private static Formula At(Formula f,string x) => Apply(f,V(x));
    private static Formula Label(string u) => Fn("coordinateLabel",P,Fn("val",V(u)));
    private static Formula Edge => Fn("coordinateEdges",P,C,B);
    private static Formula Canonical => Many("j k",FinI,Imp(Fn("B",V("j"),V("k")),Lt(V("j"),V("k"))));
    private static Formula Params(Formula body) => Many("M i",N,Many("p c",List,All("B",Rel(FinI),body)));
    private static Formula FM => Fn("Fin",Plus(M,Fn("one")));
    private static Formula Carrier => Fn("CoordinateDataCarrier",M,I);
    private static Formula Data => Fn("coordinateDataFamily",M,I);
    private static Formula Dp => Fn("fst",V("d"));
    private static Formula Dc => Fn("fst",Fn("snd",V("d")));
    private static Formula Db => Fn("snd",Fn("snd",V("d")));
    private static Formula CoerceList(Formula f) => Fn("values",f);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded weak coordinate data and literal triangular closure have exactly the same finite objects and first-column count. The coordinate description permits every zero and tie, while ordered exceptional bits make reconstruction unique.",
        H("Exact source reconstruction and coordinate counting"),
        Blocks(
            Node("Reconstruction","coordinateEdgeSet","Reconstruct the labelled finite edges",EdgeSet(),
                "Take all pairs of bounded coordinate vertices joined by coordinateEdges and apply the canonical natural label to both endpoints. This definition keeps actual edges; it contains no assumed counting formula. For a weakly increasing position list the label map is increasing and bijective onto zero through M+i.",DescribeRole.Definition),
            Node("Reconstruction","coordinateEdgeSet_mem_edgeFamily","Reconstruction preserves the complete literal family",Construct(),
                "An increasing image transports both ordered closure rules and their maxima. The endpoint labels stay between zero and n+1. The anchor is ordinary rank zero; its neighbors are exactly ordinary ranks one through M, independently of all cutoffs and exceptional bits. Filtering the image edges by first coordinate zero therefore has cardinality M. The literal edge family and its triangle-point bijection retain the repeated-point source condition and both forced conclusions.",DescribeRole.Theorem),
            Node("Reconstruction","edgeFamily_eq_coordinateEdgeSet","Every source graph has canonical weak coordinate data",Decompose(),
                "The exact source realization gives an increasing bijection into the full finite natural interval. Its range equals the range of coordinateLabel, so uniqueness of increasing enumerations identifies the two maps. Restriction and extension across the supported finite vertex set give bounded Rules. Every actual source edge then agrees with the reconstructed edge set. Exceptional bits imply increasing exceptional labels, leaving no unused reverse or loop bits.",DescribeRole.Theorem),
            Node("Reconstruction","CoordinateDataCarrier","The finite coordinate carrier",
                Many("M i",N,Eq(Carrier,Fn("Prod",Map(FinI,FM),Fn("Prod",Map(FinI,FM),Fn("Finset",Fn("Prod",FinI,FinI)))))),
                "A datum consists of a position array, a cutoff array, and a finite set of labelled exceptional edges. Both arrays take values zero through M. There are no positivity or distinctness assumptions.",DescribeRole.Definition),
            Node("Reconstruction","coordinateDataFamily","The finite admissible data family",DataFamily(),
                "Filter the finite carrier by a weakly increasing position array, exceptional bits supported on j<k, and the exact bounded closure rules. The notation values(f) in the display denotes the pointwise natural values of a Fin-valued array. Bounds are built into the carrier, and the empty exceptional index set is allowed.",DescribeRole.Definition),
            Node("Reconstruction","count_eq_coordinateDataFamily_card","Exact coordinate enumeration on every original rank",Count(),
                "Reconstruction maps the finite admissible data family into edgeFamily. For injectivity, the increasing missing anchor-neighbor labels p(j)+j+1 recover p; ordinary incidence at rank c(j)+1 distinguishes any two bounded cutoffs; the remaining increasing exceptional edges recover B. The source reconstruction supplies surjectivity. The finite bijection and the literal point-edge count bridge give the displayed equality for every valid n and i, including M=0, i=0 and n=0. The separate binomial-basis coefficient identity and its top coefficient are not asserted by this cardinality theorem.",DescribeRole.Theorem),
            Node("Reconstruction","coordinate_generic_bits","Generic admissibility forces the exceptional bits",Generic(false),
                "Assume positive strictly increasing positions, bounded cutoffs, no cutoff equal to any position, and exceptional bits supported on j<k. Transport the actual coordinate graph to the natural canonical labels. The existing generic_exceptional_edge theorem applies with the ordinary rank list and its exact Position and Cutoff statements. It forces every exceptional bit by the displayed criterion. This theorem assumes admissibility and does not count arrays.",DescribeRole.Theorem),
            Node("Reconstruction","coordinate_generic_rules_iff","The generic exceptional criterion is sufficient as well",Generic(true),
                "The forward direction uses coordinate_generic_bits. For the converse, apply the existing exists_cutoff_completion to the canonical ordinary and exceptional labels. Verify every bounded coordinate edge against that graph: ordinary clique edges, mixed cutoff incidence including rank zero, and the supplied exceptional criterion. Pullback and restriction transport both closure rules. This gives actual admissibility of the specified bits, rather than a presumed generic graph. Zero cutoffs and empty index sets remain allowed under the stated positive-position and separation hypotheses.",DescribeRole.Theorem)), []));

    private static Formula Generic(bool equivalence)
    {
        var conclusion=Many("j k",FinI,Iff(Fn("B",V("j"),V("k")),And(
            Lt(V("j"),V("k")),Lt(At(C,"j"),At(P,"k")),Lt(At(C,"k"),At(P,"j")))));
        var rules=Fn("Rules",Fn("boundedCoordinateEdges",M,P,C,B));
        var hyp=And(Fn("StrictMono",P),All("j",FinI,Le(At(P,"j"),M)),
            All("j",FinI,Le(At(C,"j"),M)),All("j",FinI,Lt(Fn("zero"),At(P,"j"))),
            Many("j k",FinI,Not(Eq(At(C,"j"),At(P,"k")))),Canonical);
        return Params(Imp(hyp,equivalence?Iff(rules,conclusion):Imp(rules,conclusion)));
    }

    private static Formula EdgeSet() => Params(Many("a b",N,Iff(Mem(Pair(V("a"),V("b")),A),
        Ex("u",T,Ex("v",T,And(Apply(Edge,Fn("val",V("u")),Fn("val",V("v"))),
            Eq(Label("u"),V("a")),Eq(Label("v"),V("b"))))))));
    private static Formula Construct()
    {
        var m=Sub(Plus(V("n"),Fn("one")),I);
        return Many("n i",N,Imp(Le(I,Plus(V("n"),Fn("one"))),Many("p c",List,All("B",Rel(FinI),
            Imp(HypAt(m),Mem(Fn("coordinateEdgeSet",m,P,C,B),Fn("edgeFamily",V("n"),m)))))));
    }
    private static Formula Decompose()
    {
        var n=V("n");var m=Sub(Plus(n,Fn("one")),I);
        var result=And(Fn("Monotone",P),All("j",FinI,Le(At(P,"j"),m)),
            All("j",FinI,Le(At(C,"j"),m)),Canonical,
            Fn("Rules",Fn("boundedCoordinateEdges",m,P,C,B)),Eq(Fn("coordinateEdgeSet",m,P,C,B),V("A")));
        return Many("n i",N,Imp(Le(I,Plus(n,Fn("one"))),All("A",Points,
            Imp(Mem(V("A"),Fn("edgeFamily",n,m)),Ex("p",List,Ex("c",List,Ex("B",Rel(FinI),result)))))));
    }
    private static Formula HypAt(Formula m) => And(Fn("Monotone",P),
        All("j",FinI,Le(At(P,"j"),m)),All("j",FinI,Le(At(C,"j"),m)),
        Fn("Rules",Fn("boundedCoordinateEdges",m,P,C,B)));
    private static Formula DataFamily() => Many("M i",N,All("d",Carrier,Iff(Mem(V("d"),Data),And(
        Fn("Monotone",CoerceList(Dp)),
        Many("j k",FinI,Imp(Mem(Pair(V("j"),V("k")),Db),Lt(V("j"),V("k")))),
        Fn("Rules",Fn("boundedCoordinateEdges",M,CoerceList(Dp),CoerceList(Dc),Fn("membership",Db)))))));
    private static Formula Count()
    {
        var n=V("n");var m=Sub(Plus(n,Fn("one")),I);
        return Many("n i",N,Imp(Le(I,Plus(n,Fn("one"))),Eq(Fn("count",n,m),Fn("card",Fn("coordinateDataFamily",m,I)))));
    }
}
