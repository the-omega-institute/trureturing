using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases.MazorchukXuGenericNotation;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

internal static class MazorchukXuGenericNotation
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

internal sealed class MazorchukXuGenericDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite position and cutoff data reconstruct the labelled source graphs and give unique generic completions.",
        H("Forced edges in generic patterns"),
        Blocks(
            Node("Generic","Position","Position relative to the ordinary list",PositionFormula(),
                "The zero-indexed list has M vertices. Exactly the indices below p occur before s, and exactly the indices at least p occur after s. The bound includes p=0 and p=M; no listed vertex equals s.",DescribeRole.Definition),
            Node("Generic","Cutoff","Incidence cutoff",CutoffFormula(),
                "The cutoff lies between zero and M. Incidence starts at the zero-indexed cutoff. Both empty and full incidence are included.",DescribeRole.Definition),
            Node("Generic","generic_exceptional_edge","The forced generic edge criterion",MainFormula(),
                "Assume the rules P and J, a list of vertices joined to zero, positions 0<ps<pt, and the two incidence cutoffs. When cs differs from pt and ct differs from ps, the edge from s to t exists exactly when cs<pt and ct<ps. Necessity uses the ordinary vertex just after s, then the vertices around t; when pt=M the latter bound follows directly from the cutoff bound. Sufficiency uses ordinary vertices immediately before s and t in J. No strict-monotonicity hypothesis on the list is needed because the position predicates already give the inequalities used in the proof. This criterion determines the exceptional edges whenever the listed generic inequalities hold.",DescribeRole.Theorem),
            Node("Generic","exists_cutoff_completion","A completion for arbitrary cutoffs",CompletionFormula(),
                "An increasing ordinary list and an injective exceptional list lie in the positive vertices up to N. Position predicates separate the two lists. Every cutoff lies between zero and M, with no distinctness requirement. Assign height zero to all nonexceptional vertices. An exceptional height is the ordinary vertex at its cutoff, or N+1 for an empty terminal segment. Join a<b exactly when both endpoints lie below the bound and each height is at most the opposite endpoint. These integer threshold edges satisfy both rules. The anchor edges, every ordinary incidence and the displayed exceptional-edge criterion follow. Zero cutoffs, coincident data and empty lists are included.",DescribeRole.Theorem),
            Node("Generic","edges_determined_by_data","Reconstruction from the finite data",ReconstructionFormula(),
                "Suppose the ordinary and exceptional lists together cover every positive vertex up to N. Two bounded graphs satisfying the rules agree if their anchor edges, their incidence cutoffs and all exceptional-edge bits agree. Ordinary-to-ordinary edges are forced by the anchor edges. The mixed pairs are determined by the cutoffs. The remaining pairs are exactly the exceptional bits. This is an equality of labelled relations, without an isomorphism quotient.",DescribeRole.Theorem),
            Node("Generic","exists_unique_generic_completion","Unique generic completion",UniqueFormula(),
                "Assume both vertex lists increase, the positive positions strictly increase, and no cutoff equals any position. Every fully specified coordinate datum then has exactly one bounded graph satisfying the rules and the prescribed anchor edges and cutoffs. Existence uses the integer threshold construction; the forced-edge criterion and reconstruction give uniqueness. This does not count the coordinate data or prove the binomial counting identity.",DescribeRole.Theorem),
            Node("Generic","exceptional_label_eq_position_add_index","Positions reconstruct the labels",LabelFormula(),
                "Let the injective ordinary list and increasing exceptional list cover all positive vertices up to N, and let p record ordinary positions. The vertices below the j-th exception split into zero, p(j) ordinary vertices and j preceding exceptions. Taking finite cardinalities gives s(j)=p(j)+j+1. The two prefix images are disjoint by the position conditions. The formula includes p(j)=0, adjacent exceptions and an empty ordinary list.",DescribeRole.Theorem),
            Node("Generic","exists_coordinate_encoding","Extraction of positions and cutoffs",EncodingFormula(),
                "Given an increasing list of anchor neighbors and an increasing list of missing anchor neighbors covering the positive vertices, every graph satisfying the rules yields a monotone position list and one cutoff for each exception. Prefix cardinality supplies each position; monotonicity follows because an ordinary vertex cannot lie before an earlier exception and after a later one. The cutoff theorem supplies the incidence data, and prefix partitioning reconstructs the original natural labels. This extracts the coordinates but does not yet identify their compression classes or enumerate them.",DescribeRole.Theorem),
            Node("Generic","edgeFamily_has_coordinates","Coordinates of the literal finite family",SourceEncodingFormula(),
                "For every natural n and every deficit i at most n+1, a member of edgeFamily with n+1-i anchor edges has an increasing ordinary list of length n+1-i and an increasing exceptional list of length i. Sort the actual anchor-neighbor set and its complement in one through n+1. Their cardinalities give the two list lengths. The lists cover the entire positive vertex interval; position and cutoff extraction then gives all the displayed coordinates and exact exceptional labels. The notation pairMembership(A)(a,b) means (a,b) belongs to A. The point-to-edge counted equivalence identifies this with the literal source family. This supplies extraction for every valid source parameter, including i=n+1; a two-way compressed-pattern bijection and its cardinality are still needed.",DescribeRole.Theorem)), []));

    private static Formula PositionFormula()
    {
        var M=V("M");var g=V("g");var s=V("s");var p=V("p");var r=V("r");
        var conditions=And(Le(p,M),All("r",Fn("Fin",M),And(
            Iff(Lt(Fn("g",r),s),Lt(Fn("val",r),p)),
            Iff(Lt(s,Fn("g",r)),Le(p,Fn("val",r))))));
        return All("M",N,All("g",Map(Fn("Fin",M),N),Many("s p",N,
            Iff(Fn("Position",g,s,p),conditions))));
    }
    private static Formula CutoffFormula()
    {
        var M=V("M");var E=V("E");var g=V("g");var s=V("s");var c=V("c");var r=V("r");
        var conditions=And(Le(c,M),All("r",Fn("Fin",M),
            Iff(Fn("Incident",E,s,Fn("g",r)),Le(c,Fn("val",r)))));
        return All("M",N,All("E",Rel(N),All("g",Map(Fn("Fin",M),N),Many("s c",N,
            Iff(Fn("Cutoff",E,g,s,c),conditions)))));
    }
    private static Formula MainFormula()
    {
        var M=V("M");var E=V("E");var g=V("g");var s=V("s");var t=V("t");
        var ps=V("ps");var pt=V("pt");var cs=V("cs");var ct=V("ct");
        var hypothesis=And(Fn("Rules",E),All("r",Fn("Fin",M),Fn("E",D(0),Fn("g",V("r")))),
            Lt(D(0),ps),Lt(ps,pt),Fn("Position",g,s,ps),Fn("Position",g,t,pt),
            Fn("Cutoff",E,g,s,cs),Fn("Cutoff",E,g,t,ct),Not(Eq(cs,pt)),Not(Eq(ct,ps)));
        var conclusion=Iff(Fn("E",s,t),And(Lt(cs,pt),Lt(ct,ps)));
        return All("E",Rel(N),All("M",N,All("g",Map(Fn("Fin",M),N),
            Many("s t ps pt cs ct",N,Imp(hypothesis,conclusion)))));
    }
    private static Formula Lists(Formula body)
    {
        var M=V("M");var i=V("i");
        return Many("N M i",N,All("g",Map(Fn("Fin",M),N),All("s",Map(Fn("Fin",i),N),
            All("p",Map(Fn("Fin",i),N),All("c",Map(Fn("Fin",i),N),body)))));
    }
    private static Formula Bounds()
    {
        var M=V("M");var i=V("i");var r=V("r");var j=V("j");
        return And(Fn("StrictMono",V("g")),All("r",Fn("Fin",M),And(Lt(D(0),Fn("g",r)),Le(Fn("g",r),V("N")))),
            All("j",Fn("Fin",i),And(Lt(D(0),Fn("s",j)),Le(Fn("s",j),V("N")),
                Fn("Position",V("g"),Fn("s",j),Fn("p",j)),Le(Fn("c",j),M))));
    }
    private static Formula Cover()
    {
        var a=V("a");return All("a",N,Imp(And(Lt(D(0),a),Le(a,V("N"))),Or(
            Ex("r",Fn("Fin",V("M")),Eq(Fn("g",V("r")),a)),
            Ex("j",Fn("Fin",V("i")),Eq(Fn("s",V("j")),a)))));
    }
    private static Formula Bounded(Formula E) => Many("a b",N,
        Imp(Apply(E,V("a"),V("b")),Le(V("b"),V("N"))));
    private static Formula Cutoffs(Formula E) => All("j",Fn("Fin",V("i")),
        Fn("Cutoff",E,V("g"),Fn("s",V("j")),Fn("c",V("j"))));
    private static Formula CompletionFormula()
    {
        var E=V("E");var a=V("a");var j=V("j");var k=V("k");var i=V("i");
        var anchor=All("a",N,Iff(Fn("E",D(0),a),And(Lt(D(0),a),Le(a,V("N")),
            All("j",Fn("Fin",i),Not(Eq(Fn("s",j),a))))));
        var bits=All("j",Fn("Fin",i),All("k",Fn("Fin",i),Imp(Lt(Fn("s",j),Fn("s",k)),
            Iff(Fn("E",Fn("s",j),Fn("s",k)),And(Lt(Fn("c",j),Fn("p",k)),Lt(Fn("c",k),Fn("p",j)))))));
        return Lists(Imp(And(Bounds(),Fn("Injective",V("s"))),Ex("E",Rel(N),
            And(Fn("Rules",E),Bounded(E),anchor,Cutoffs(E),bits))));
    }
    private static Formula ReconstructionFormula()
    {
        var E=V("E");var F=V("F");var i=V("i");var M=V("M");
        var hypothesis=And(Fn("Rules",E),Fn("Rules",F),Bounded(E),Bounded(F),Cover(),
            All("r",Fn("Fin",M),Fn("E",D(0),Fn("g",V("r")))),
            All("a",N,Iff(Fn("E",D(0),V("a")),Fn("F",D(0),V("a")))),Cutoffs(E),Cutoffs(F),
            All("j",Fn("Fin",i),All("k",Fn("Fin",i),
                Iff(Fn("E",Fn("s",V("j")),Fn("s",V("k"))),Fn("F",Fn("s",V("j")),Fn("s",V("k")))))));
        return Many("N M i",N,All("E",Rel(N),All("F",Rel(N),
            All("g",Map(Fn("Fin",M),N),All("s",Map(Fn("Fin",i),N),All("c",Map(Fn("Fin",i),N),
                Imp(hypothesis,Eq(E,F))))))));
    }
    private static Formula UniqueFormula()
    {
        var i=V("i");var j=V("j");var k=V("k");var E=V("E");var F=V("F");
        Formula data(Formula relation) => And(Fn("Rules",relation),Bounded(relation),
            All("a",N,Iff(Apply(relation,D(0),V("a")),Ex("r",Fn("Fin",V("M")),Eq(Fn("g",V("r")),V("a"))))),
            Cutoffs(relation));
        var hypothesis=And(Bounds(),Fn("StrictMono",V("s")),Fn("StrictMono",V("p")),
            All("j",Fn("Fin",i),Lt(D(0),Fn("p",j))),
            All("j",Fn("Fin",i),All("k",Fn("Fin",i),Not(Eq(Fn("c",j),Fn("p",k))))),Cover());
        return Lists(Imp(hypothesis,Ex("E",Rel(N),And(data(E),All("F",Rel(N),Imp(data(F),Eq(F,E)))))));
    }

    private static Formula Labels() => All("j",Fn("Fin",V("i")),
        Eq(Fn("s",V("j")),Plus(Plus(Fn("p",V("j")),Fn("val",V("j"))),D(1))));
    private static Formula LabelFormula()
    {
        var M=V("M");var i=V("i");var j=V("j");
        var hypothesis=And(Fn("Injective",V("g")),Fn("StrictMono",V("s")),
            All("r",Fn("Fin",M),Lt(D(0),Fn("g",V("r")))),
            All("j",Fn("Fin",i),And(Lt(D(0),Fn("s",j)),Le(Fn("s",j),V("N")),
                Fn("Position",V("g"),Fn("s",j),Fn("p",j)))),Cover());
        return Many("N M i",N,All("g",Map(Fn("Fin",M),N),All("s",Map(Fn("Fin",i),N),
            All("p",Map(Fn("Fin",i),N),Imp(hypothesis,Labels())))));
    }
    private static Formula EncodingFormula()
    {
        var E=V("E");var M=V("M");var i=V("i");var j=V("j");
        var hypothesis=And(Fn("Rules",E),Fn("StrictMono",V("g")),Fn("StrictMono",V("s")),
            All("r",Fn("Fin",M),Fn("E",D(0),Fn("g",V("r")))),
            All("j",Fn("Fin",i),And(Not(Fn("E",D(0),Fn("s",j))),Lt(D(0),Fn("s",j)),Le(Fn("s",j),V("N")))),Cover());
        var conclusion=Ex("p",Map(Fn("Fin",i),N),Ex("c",Map(Fn("Fin",i),N),
            And(Fn("Monotone",V("p")),All("j",Fn("Fin",i),
                Fn("Position",V("g"),Fn("s",j),Fn("p",j))),Cutoffs(E),Labels())));
        return Many("N M i",N,All("E",Rel(N),All("g",Map(Fn("Fin",M),N),
            All("s",Map(Fn("Fin",i),N),Imp(hypothesis,conclusion)))));
    }

    private static Formula SourceEncodingFormula()
    {
        var n=V("n");var i=V("i");var A=V("A");var a=V("a");var j=V("j");
        var g=V("g");var s=V("s");var p=V("p");var c=V("c");
        var Nn=Plus(n,D(1));var M=Sub(Nn,i);var si=Fn("s",j);
        var cover=All("a",N,Imp(And(Lt(D(0),a),Le(a,Nn)),Or(
            Ex("r",Fn("Fin",M),Eq(Fn("g",V("r")),a)),
            Ex("j",Fn("Fin",i),Eq(si,a)))));
        var anchor=All("a",N,Iff(Mem(Pair(D(0),a),A),Ex("r",Fn("Fin",M),Eq(Fn("g",V("r")),a))));
        var missing=All("j",Fn("Fin",i),And(Not(Mem(Pair(D(0),si),A)),Lt(D(0),si),Le(si,Nn)));
        var positions=All("j",Fn("Fin",i),Fn("Position",g,si,Fn("p",j)));
        var cutoffs=All("j",Fn("Fin",i),Fn("Cutoff",Fn("pairMembership",A),g,si,Fn("c",j)));
        var conclusion=And(Fn("StrictMono",g),Fn("StrictMono",s),Fn("Monotone",p),anchor,missing,
            cover,positions,cutoffs,Labels());
        var exists=Ex("g",Map(Fn("Fin",M),N),Ex("s",Map(Fn("Fin",i),N),
            Ex("p",Map(Fn("Fin",i),N),Ex("c",Map(Fn("Fin",i),N),conclusion))));
        return Many("n i",N,All("A",Points,Imp(And(Le(i,Nn),Mem(A,Fn("edgeFamily",n,M))),exists)));
    }

}
