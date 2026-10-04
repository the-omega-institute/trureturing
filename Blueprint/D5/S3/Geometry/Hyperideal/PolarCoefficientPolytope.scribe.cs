using System;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class PolarCoefficientPolytopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered endpoint completeness and all labeled supporting intersections of a polar coefficient polytope.",
        H("Marked coefficient polytopes"),
        Blocks(
            Paragraph(Text("Let I=Fin(4), Coeff=I->Real and Mat=I->I->Real. Admissible(G) means "
                + "G(i,i)=1 for every i, G(i,j)<-1 for every distinct i,j, and G(i,j)=G(j,i) "
                + "for every i,j. Each of the six off-diagonal entries varies independently. "
                + "Set row(G,a,i)=sum_j G(i,j)a(j), and define P(G) literally by a(j)>=0, "
                + "sum_j a(j)=1, and row(G,a,i)<=0 for every i.")),
            Paragraph(Text("For distinct i,j define b(G,i,j) to have coordinate -G(i,j)/(1-G(i,j)) "
                + "at i, 1/(1-G(i,j)) at j and zero elsewhere. E(G) is the set of all these "
                + "ordered endpoints. ext(P(G)) denotes the real extreme-point set. "
                + "For S,T:Finset(I), F(G,S,T) consists of a in P(G) with a(h)=0 for every "
                + "h in S and row(G,a,k)=0 for every k in T. V(G,S,T) is the set of b(G,i,j) "
                + "with i!=j, h!=i and h!=j for every h in S, and k=i for every k in T. "
                + "hull is real convex hull; coord(a,k) denotes a(k).")),
            Describe.Lean(
                DescribeId.Create("marked-coefficient-classification"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/PolarCoefficientPolytope.marked_coefficient_classification"),
                H("Exact ordered vertices and simultaneous supporting-face hulls"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A nonnegative row forces its own coefficient to exceed one half, "
                        + "so at most one row can be active. If no row is active, a mass-preserving "
                        + "direction on two positive coordinates admits feasible perturbations in "
                        + "both signs. If the active row i has three positive coordinates i,j,k, "
                        + "the actual direction (G(i,j)-G(i,k))e_i+(G(i,k)-1)e_j+(1-G(i,j))e_k "
                        + "has zero mass and active row, and is nonzero.")),
                    Paragraph(Text("Continuity preserves every inactive strict row and positive coordinate "
                        + "for sufficiently small perturbations of both signs. Extremality therefore "
                        + "forces exactly two positive coordinates and one active row. The mass "
                        + "and active-row equations determine the displayed ordered endpoint. "
                        + "Direct supporting equations prove the converse and ordered injectivity. "
                        + "The existing compact convex hull and extreme-face results then give "
                        + "all simultaneous labeled supporting-intersection hulls.")),
                    Paragraph(Text("Taking G(i,j)=-x(i,j) covers the original independent source box "
                        + "1<x(i,j)<=2, including equal-length fibers, with original six-input "
                        + "ordering (x12,x13,x14,x34,x24,x23). There are twelve distinct ordered "
                        + "endpoints. Empty label sets give the whole hull; one row label gives "
                        + "three endpoints, one zero-coordinate label gives six endpoints, and "
                        + "two distinct row labels give an empty intersection.")),
                    Paragraph(Text("This is a coefficient-polytope classification. It supplies no affine "
                        + "facet dimension, oriented hexagon parametrization, Lorentz/Klein "
                        + "identification, marked-cell homeomorphism, face gluing, manifold, "
                        + "curvature or completeness conclusion."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var g=F.Id("G"); var i=F.Id("i"); var j=F.Id("j");
        var k=F.Id("k"); var l=F.Id("l"); var s=F.Id("S"); var t=F.Id("T");
        var z=F.D(0); var b=Call("b",g,i,j); var c=Call("b",g,k,l);
        var incidence=All("i",I,All("j",I,Imp(Ne(i,j),And(
            In(b,Call("P",g)),
            All("k",I,Iff(Eq(Call("row",g,b,k),z),Eq(k,i))),
            All("k",I,Imp(Ne(k,i),Lt(Call("row",g,b,k),z))),
            All("k",I,Iff(Eq(Call("coord",b,k),z),And(Ne(k,i),Ne(k,j))))))));
        var injectivity=All("i",I,All("j",I,All("k",I,All("l",I,
            Imp(And(Ne(i,j),Ne(k,l),Eq(b,c)),And(Eq(i,k),Eq(j,l)))))));
        var intersections=All("S",Call("Finset",I),All("T",Call("Finset",I),
            Eq(Call("F",g,s,t),Call("hull",Call("V",g,s,t)))));
        return All("G",new Formula.NamedConstant(FormulaIdentifier.Create("Mat")),
            Imp(Call("Admissible",g),And(Eq(Call("ext",Call("P",g)),Call("E",g)),
                And(incidence,injectivity),intersections)));
    }
    private static Formula I => new Formula.NamedConstant(FormulaIdentifier.Create("I"));
    private static Formula Call(string n,params Formula[] a) => new Formula.FunctionCall(FormulaIdentifier.Create(n),[..a]);
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.NotEqual,b);
    private static Formula Lt(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula In(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.MemberOf,b);
    private static Formula Iff(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula All(string v,Formula d,Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(v),d,b);
    private static Formula And(params Formula[] a)
    {
        if(a.Length==0)throw new ArgumentException("Empty conjunction");
        var r=a[^1];for(var i=a.Length-2;i>=0;i--)r=new Formula.Logic(a[i],FormulaLogicOperator.And,r);return r;
    }
}
