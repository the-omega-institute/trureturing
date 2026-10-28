using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class TotalDominationDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/TotalDominationDensity.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual total-domination roots approximate every complex target with unbounded finite graph order.",
        H("Whole-plane density of actual total-domination roots"), Blocks(
            Paragraph(Text("The target is the original WholePlaneDensity from TotalDominationSeeds: for every complex z and every positive real epsilon, an actual simple undirected graph G on Fin n, n>=2, has no isolated vertices, its literal complex total-domination subset-count polynomial is nonzero, and an actual root w satisfies norm(w-z)<epsilon. IsTotal requires a selected neighbour for every vertex, including every selected vertex. No ordinary, independent or clique-domination polynomial is substituted.")),
            Node("roots_approximate_exp_nonunit", "Actual roots at every nonunit logarithmic radius", Density(true),
                "For every complex xi with xi.re nonzero and every positive real epsilon there exist n>=2, an actual isolate-free SimpleGraph G on Fin n, and a complex root w of the same nonzero complexPolynomial G such that norm(w-(exp(xi)-1))<epsilon. Joint power-root approximation chooses a threshold N. If xi.re>0, use a friendship root r below -(exp((N+3)*xi.re)+2), t=log(-(1+r)), and alpha=pi. If xi.re<0, use a genuine small positive shift 1+r<exp((N+3)*xi.re), t=log(1+r), and alpha=0. In both cases N+2<t/xi.re and exp(t+alpha*I)=1+r. The joint lemma gives one k and u; labelled_root_blowup supplies one actual Fin n graph whose polynomial has root u-1. Nonzeroness and the no-isolate property are proved for that same graph."),
            Node("roots_approximate_exp", "The unit-circle boundary follows by continuity", Density(false),
                "For every complex xi, including xi.re=0, and every positive epsilon there is an actual finite labelled isolate-free graph of order at least two with a nonzero actual total-domination polynomial and a root within epsilon of exp(xi)-1. For zero real part choose positive delta from continuity of exp at xi with tolerance epsilon/2, perturb xi by the positive real delta/2, apply the nonunit theorem with epsilon/2, and add the two errors. This pays the boundary with the same actual witness graph."),
            Node("result", "The exact original whole-plane target", Whole(),
                "The theorem has literal type TotalDominationSeeds.WholePlaneDensity. For arbitrary complex z and real epsilon>0, if 1+z=0 use the genuine seed roots accumulating at -1. Otherwise apply roots_approximate_exp at log(1+z); the existing exact identity exp(log(1+z))=1+z identifies the target. The resulting witness is an actual finite simple undirected graph on Fin n with n>=2 and no isolated vertices, its actual subset-count total-domination polynomial is nonzero, and the same actual complex root is within epsilon of z. This is the whole-plane density conclusion for the actual total-domination polynomial."),
            Paragraph(Text("The cone, disjoint-union, friendship and independent-fibre substitution formulas are known consumed ingredients; see the provenance in TotalDominationSeeds and TotalDominationBlowup. The direct route does not assume ordinary domination-root density or a conditional total-density supplier. The published whole-question source is Shao and Zhao, arXiv:2609.06569v5, section 5.2 Open Problem 2. The proof concerns the stated polynomial and does not assert literature priority."))), []));

    private static DocumentBlock Node(string selector, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("td-density-" + selector.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + selector),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Combinatorics/shao2026connectedroots")), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula V(string s) => F.Id(s);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula Par(Formula x) => Seq(Open,x,Close);
    private static Formula Cast(Formula x, Formula t) => Par(Seq(x,Colon,t));
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Subtract,y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.NotEqual,y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThan,y);
    private static Formula Leq(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula And(params Formula[] xs) => xs.Length==1 ? xs[0] : new Formula.Logic(Par(xs[0]),FormulaLogicOperator.And,Par(And(xs[1..])));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x),FormulaLogicOperator.Implies,Par(y));
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall,Sp,Par(Seq(V(s),Colon,t)),Comma,Sp,b);
    private static Formula Some(string s, Formula t, Formula b) => Seq(Exists,Sp,Par(Seq(V(s),Colon,t)),Comma,Sp,b);
    private static Formula Graph(Formula t) => Call("SimpleGraph",t);
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Adj(Formula g, Formula v, Formula u) => Call("Adj",g,v,u);
    private static Formula Poly(Formula g, bool complex=true) => Call(complex?"complexPolynomial":"totalPolynomial",g);
    private static Formula Root(Formula p, Formula w) => Call("IsRoot",p,w);
    private static Formula Norm(Formula x) => Seq(Vert,Sp,x,Vert);
    private static Formula NoIso(Formula g, Formula t) => All("v",t,Some("u",t,Adj(g,V("v"),V("u"))));
    private static Formula Witness(Formula target) => Some("n",Nat,Some("G",Graph(Fin(V("n"))),Some("w",Complex,And(Leq(D(2),V("n")),NoIso(V("G"),Fin(V("n"))),Ne(Poly(V("G")),D(0)),Root(Poly(V("G")),V("w")),Lt(Norm(Sub(V("w"),target)),V("epsilon"))))));
    private static Formula Whole() => All("z",Complex,All("epsilon",Real,Imp(Lt(D(0),V("epsilon")),Witness(V("z")))));
    private static Formula Density(bool nonunit) => All("xi",Complex,nonunit?Imp(Ne(Call("re",V("xi")),D(0)),DensityEpsilon()):DensityEpsilon());
    private static Formula DensityEpsilon() => All("epsilon",Real,Imp(Lt(D(0),V("epsilon")),Witness(Sub(Call("exp",V("xi")),Cast(D(1),Complex)))));
}
