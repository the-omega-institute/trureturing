using System.Collections.Generic;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class PartialTwoTreePsdCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One simultaneous angle extension supplies real rank-three completion on every finite partial two-tree.",
        H("Simultaneous Partial Two-Tree Completion"),
        Blocks(
            Describe.Lean(DescribeId.Create("partial-two-tree-joint-angle-table"),
                DeclarationHandle.Create("D5/S3/QuadraticForms/PartialTwoTreePsdCompletion.exists_joint_angle_table"),
                H("A single joint angle table"), StatementSource.FromAuthor(Disp(AngleStatement())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/laurent1994seriesparallel")),
                Blocks(
                    Paragraph(Text("V is an arbitrary finite type, including the empty type. G is a simple graph on V. The real table theta is symmetric, has zero diagonal, and has values in [0,pi] on G-edges. The cycle condition below ranges over every natural m at least three, every injective c from Fin m into V following G-edges, and every odd-cardinality subset F of Fin m. The successor next is finRotate m, or addition of one modulo m; complement is inside Fin m. No global realization, fill values, or compatible family of cycle completions is an input.")),
                    Paragraph(Text("The conclusion constructs one symmetric table Gamma, with zero diagonal and all values in [0,pi], preserving every G-edge of theta. For all ordered triples a,b,c, Gamma(a,b) is at most Gamma(a,c)+Gamma(c,b), and Gamma(a,b)+Gamma(b,c)+Gamma(c,a) is at most 2pi. Repeated vertices are allowed in these triple statements. Thus the same fill-edge value serves all incident triangles in any chosen chordal supergraph.")),
                    Paragraph(Text("Use a signed copy V times Bool. An edge costs theta when its signs agree and pi-theta when they differ. The simple-cycle inequalities imply a cost of at least pi for every projected closed walk with opposite endpoint signs. At a repeated projected vertex, opposite signs isolate a shorter odd loop, while equal signs allow deletion of a nonnegative-cost segment. The remaining elementary walks are simple cycles or length-two backtracks.")),
                    Paragraph(Text("For a missing pair u,v, the new angle is the supremum of zero and pi minus the cost of every odd signed u-to-v path. Nonnegative edge costs bound this supremum by pi. Joining an even path with an odd path gives every upper bound required by that same value. On the four signed endpoint states, equal vertices have distance zero or pi; unequal vertices have distance x or pi-x. These distances satisfy the triangle inequality. Split a new walk at its first new edge to preserve all boundary distances, then close it with the sign-flipped original prefix to preserve every odd closed-walk inequality. A maximal feasible graph on the finite carrier is complete. The resulting table, rather than a collection of individually chosen cycle witnesses, is the live construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("partial-two-tree-rank-three-criterion"),
                DeclarationHandle.Create("D5/S3/QuadraticForms/PartialTwoTreePsdCompletion.partial_two_tree_rank_three_iff"),
                H("The exact rank-three criterion"), StatementSource.FromAuthor(Disp(CompletionStatement())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/laurent1994seriesparallel")),
                Blocks(
                    Paragraph(Text("A is any real symmetric matrix on V with diagonal one and G-edge entries in the closed interval [-1,1]. The graph hypothesis is the existence of a simple graph H on the same V containing G, with H chordal and every H-clique C satisfying Nat.card C at most three. A clique is a subset C of V, so the hypothesis includes all cliques and the empty clique. No prescribed H-edge values are assumed. The graph condition is used directly, with no unproved replacement by a minor condition.")),
                    Paragraph(Text("There exists a real PSD matrix B on V of real matrix rank at most three, diagonal one, and B(i,j)=A(i,j) on every G-edge, if and only if all the displayed simple-cycle inequalities hold for theta_A(i,j)=arccos(A(i,j)). The finite carrier, real data, cycles and odd subsets are all universally quantified. Empty and disconnected graphs, entries at both closed endpoints, repeated realization vectors, singular completions and nonspanning configurations remain in scope.")),
                    Paragraph(Text("For sufficiency, construct the joint table from theta_A, and set T(i,j)=cos(Gamma(i,j)). Each clique of H has at most three elements. For a nonempty clique, inject it into Fin 3 and use a left inverse to enumerate its vertices in three slots, repeating vertices where necessary. The three-cycle inequalities follow from the ordinary triangle inequalities and perimeter bound. Directly apply CycleRankThreePsdCompletion.cycle_rank_three_iff, then restrict its PSD matrix to the clique. The clique rank bound follows from its cardinality. Empty cliques use the empty matrix. Directly apply RankBoundedChordalPsdCompletion.exists_posSemidef_completion_rank_le with d=3 to T and H; cosine of arccos restores the original G-edge entries.")),
                    Paragraph(Text("For necessity, restrict B to each injective Fin m cycle. Positive semidefiniteness survives submatrix restriction and rank cannot increase. The existing cycle criterion gives exactly that cycle's odd-subset inequalities. This is a static existence theorem, with no uniqueness, algorithmic complexity, physical realization, or empirical claim. The classical source establishes feasibility; the uniform rank-three bound here uses the separate rank-controlled chordal assembly result."))),
                DescribeRole.Theorem))));

    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Val(Formula t, params Formula[] args) => Call("value", new[] { t }.Concat(args).ToArray());
    private static Formula And(params Formula[] clauses) => Join(Land, clauses.Select(c => Seq(Open, c, Close)).ToArray());
    private static Formula Join(Formula relation, Formula[] clauses)
    {
        var parts = new List<Formula>();
        foreach (var clause in clauses) { if (parts.Count > 0) { parts.Add(Sp); parts.Add(relation); parts.Add(Sp); } parts.Add(clause); }
        return Seq(parts.ToArray());
    }
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Plus(params Formula[] args) => Join(PlusToken, args);
    private static Formula PlusToken => F.Plus;
    private static Formula Arrow(Formula a, Formula b) => Seq(Open, a, Close, Sp, Rightarrow, Sp, Open, b, Close);
    private static Formula Typed(Formula name, Formula type) => Seq(Open, name, Sp, Colon, Sp, type, Close);
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Some(Formula name, Formula type, Formula body) => Seq(Exists, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Finite(Formula v, Formula body) => Seq(OpenBracket, Call("Finite", v), CloseBracket, Comma, Sp, body);
    private static Formula Table(Formula v) => Seq(v, Sp, To, Sp, v, Sp, To, Sp, R);
    private static Formula Sym(Formula v, Formula t) { var a=F.Id("a"); var b=F.Id("b"); return All(a,v,All(b,v,Eqn(Val(t,a,b),Val(t,b,a)))); }
    private static Formula Diag(Formula v, Formula t, Formula d) { var a=F.Id("a"); return All(a,v,Eqn(Val(t,a,a),d)); }
    private static Formula Bounds(Formula v, Formula t, Formula? g, Formula lower, Formula upper)
    {
        var a=F.Id("a"); var b=F.Id("b"); var range=And(Le(lower,Val(t,a,b)),Le(Val(t,a,b),upper));
        return All(a,v,All(b,v,g is null ? range : Arrow(Call("Adj",g,a,b),range)));
    }
    private static Formula Preserve(Formula v, Formula g, Formula t, Formula s)
    {
        var a=F.Id("a"); var b=F.Id("b"); return All(a,v,All(b,v,Arrow(Call("Adj",g,a,b),Eqn(Val(t,a,b),Val(s,a,b)))));
    }
    private static Formula Cycles(Formula v, Formula g, Formula t)
    {
        var m=F.Id("m"); var c=F.Id("c"); var i=F.Id("i"); var f=F.Id("F"); var index=Call("Fin",m);
        var next=Call("next",m,i); var angle=Val(t,Val(c,i),Val(c,next));
        Formula SumAt(Formula set) => Seq(new Formula.Subscript(Sum,Seq(i,Sp,InMacro,Sp,set)),Sp,angle);
        var inequality=Le(Seq(SumAt(f),Sp,Minus,Sp,SumAt(Call("complement",f))),
            Seq(Open,Call("realcard",f),Sp,Minus,Sp,D(1),Close,Sp,Pi));
        return All(m,N,Arrow(Le(D(3),m),All(c,Seq(index,Sp,To,Sp,v),
            Arrow(And(Call("Injective",c),All(i,index,Call("Adj",g,Val(c,i),Val(c,next)))),
                All(f,Call("Finset",index),Arrow(Call("Odd",Call("card",f)),inequality))))));
    }
    private static Formula AngleStatement()
    {
        var v=F.Id("V"); var g=F.Id("G"); var t=F.Id("theta"); var q=F.Id("Gamma");
        var a=F.Id("a"); var b=F.Id("b"); var c=F.Id("c");
        Formula Triples(Formula body) => All(a,v,All(b,v,All(c,v,body)));
        var conclusion=Some(q,Table(v),And(Sym(v,q),Diag(v,q,D(0)),Bounds(v,q,null,D(0),Pi),Preserve(v,g,q,t),
            Triples(Le(Val(q,a,b),Plus(Val(q,a,c),Val(q,c,b)))),
            Triples(Le(Plus(Val(q,a,b),Val(q,b,c),Val(q,c,a)),Seq(D(2),Sp,Pi)))));
        return All(v,Call("Type"),Finite(v,All(g,Call("SimpleGraph",v),All(t,Table(v),
            Arrow(And(Sym(v,t),Diag(v,t,D(0)),Bounds(v,t,g,D(0),Pi),Cycles(v,g,t)),conclusion)))));
    }
    private static Formula CompletionStatement()
    {
        var v=F.Id("V"); var g=F.Id("G"); var h=F.Id("H"); var c=F.Id("C"); var a=F.Id("A"); var b=F.Id("B");
        var graph=Some(h,Call("SimpleGraph",v),And(Le(g,h),Call("IsChordal",h),
            All(c,Call("Set",v),Arrow(Call("IsClique",h,c),Le(Call("Natcard",c),D(3))))));
        var completion=Some(b,Call("Matrix",v,v,R),And(Call("PosSemidef",b),Le(Call("rank",b),D(3)),Diag(v,b,D(1)),Preserve(v,g,b,a)));
        var criterion=Seq(Open,completion,Close,Sp,Iff,Sp,Open,Cycles(v,g,Call("angle",a)),Close);
        return All(v,Call("Type"),Finite(v,All(g,Call("SimpleGraph",v),Arrow(graph,
            All(a,Call("Matrix",v,v,R),Arrow(And(Sym(v,a),Diag(v,a,D(1)),Bounds(v,a,g,Seq(Minus,D(1)),D(1))),criterion))))));
    }
}
