using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class ChainLocalDevelopmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Source maps that are short near a complete orbit give lower bounds for the original global chain distance, including chains through paired faces.",
        H("Local developments across original gluing faces"),
        Blocks(
            Paragraph(Text("Let I and J be types in independent universes, X an I-indexed family of extended metric spaces, and A(X) their original disjoint union. The datum G is FiniteOrbitChainMetric.Datum. Write Rel(G,a,b) for its complete original equivalence relation and delta(G,x,y) for the infimum of costs of all original finite chains from x to y. Paid source moves have their original extended distance as cost; either direction of an actual gluing costs zero.")),
            Paragraph(Text("Let Y be an extended metric space and f:A(X) to Y. Respects(G,f) means that Rel(G,b,c) implies f(b)=f(c) for every pair b,c. For a in A(X), Short(G,a,f,R) means the following for every source piece i and every c in X(i) related to a: for every x,y in X(i) with edist(c,x)<R and edist(c,y)<R, edist(f(i,x),f(i,y)) is at most edist(x,y). No distance bound is assumed for a source move outside these balls.")),
            Paragraph(Text("Guard(G,a,R) is the conjunction of two incidence conditions. For every generator j, every center c in its source piece related to a, and every x in its actual domain, edist(c,x)<R implies that c also lies in that domain. The second condition replaces source and domain by target and actual range. Both conditions use every actual generator, including inverse moves and self-gluings.")),
            Paragraph(Text("For x in A(X), first(x) is its source index and second(x) its original point. The expression Point(i,c) denotes the corresponding point of A(X). A radius r in NNReal is finite when viewed as an extended real, and all extended-distance comparisons below use that coercion.")),
            Describe.Lean(DescribeId.Create("local-development-distance-lower-bound"),
                DeclarationHandle.Create("D5/S3/Topology/ChainLocalDevelopment.local_development_distance_le"),
                H("The developed distance bounds every original chain"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The two endpoints may lie near different representatives of the complete orbit, and chains may cross the actual gluing faces. The hypotheses do not require finite index types, compact pieces, finite diameter or an attained chain infimum. They explicitly require the local incidence guards; this statement does not construct a radius satisfying those guards.")),
                    Paragraph(Text("Put a source center beside the starting point and follow it through a chain of cost less than 2r. At every stage its source displacement to the current endpoint is at most the initial displacement plus the accumulated cost, hence less than 3r. A paid move therefore has both endpoints in the same controlled source ball, where Short bounds its developed distance. At a forward gluing the domain guard places the center in the same actual domain, so the partial isometry transports it and preserves its displacement. The range guard does the same for an inverse gluing. Respects makes the developed point unchanged across either gluing. Induction bounds the developed endpoint distance by the accumulated cost for every finite chain, without a length bound.")),
                    Paragraph(Text("Each endpoint develops within r of f(a), since its nearby orbit center has the same f-value as a. Their developed distance is therefore less than 2r. Any original chain cheaper than that distance falls under the preceding estimate and contradicts it. Taking the infimum over all original chains gives the displayed lower bound.")))),
            Paragraph(Text("This is a sufficient lower-bound principle for a local model. It does not assert equality of model and quotient distances. A local isometry also needs a reverse comparison, for example by lifting sufficiently short model paths into compatible source pieces. Constructing hyperbolic charts, checking their actual face transports and local nonexpansion, and supplying their incidence guards are additional geometric conditions.")))));

    private static Formula Statement()
    {
        var G=Id("G"); var a=Id("a"); var f=Id("f"); var r=Id("r");
        var x=Id("x"); var y=Id("y"); var c=Id("c"); var d=Id("d");
        var A=Call("A",Id("X"));
        var three=F.Seq(F.D(3),F.Sp,r);
        var premises=And(Call("Respects",G,f),Lt(F.D(0),r),
            Call("Short",G,a,f,three),Call("Guard",G,a,three),
            Call("Rel",G,a,Call("Point",Call("first",x),c)),
            Call("Rel",G,a,Call("Point",Call("first",y),d)),
            Lt(Call("edist",c,Call("second",x)),r),
            Lt(Call("edist",d,Call("second",y)),r));
        var result=Implies(premises,Le(Call("edist",App(f,x),App(f,y)),Call("delta",G,x,y)));
        result=All("c",Call("X",Call("first",x)),All("d",Call("X",Call("first",y)),result));
        result=All("x",A,All("y",A,result));
        result=All("r",Id("NNReal"),result);
        result=All("a",A,result);
        result=All("f",new Formula.TypeArrow(A,Id("Y")),result);
        result=All("Y",Id("Types"),F.Seq(F.OpenBracket,Call("EMetricSpace",Id("Y")),F.CloseBracket,F.Sp,result));
        result=All("G",Call("Datum",Id("I"),Id("J"),Id("X")),result);
        result=F.Seq(F.OpenBracket,All("i",Id("I"),Call("EMetricSpace",Call("X",Id("i")))),F.CloseBracket,F.Sp,result);
        return All("I",Id("Types"),All("J",Id("Types"),All("X",new Formula.TypeArrow(Id("I"),Id("Types")),result)));
    }
    private static Formula Id(string s)=>F.Id(s);
    private static Formula Call(string s,params Formula[] xs)=>new Formula.Apply(Id(s),[..xs]);
    private static Formula App(Formula f,params Formula[] xs)=>new Formula.Apply(f,[..xs]);
    private static Formula All(string s,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,b);
    private static Formula And(params Formula[] xs)
    {
        var r=xs[^1];for(var i=xs.Length-2;i>=0;i--)r=new Formula.Logic(xs[i],FormulaLogicOperator.And,r);return r;
    }
    private static Formula Lt(Formula a,Formula b)=>F.Seq(a,F.Sp,F.Lt,F.Sp,b);
    private static Formula Le(Formula a,Formula b)=>F.Seq(a,F.Sp,F.Le,F.Sp,b);
    private static Formula Implies(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
}
