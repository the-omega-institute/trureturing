using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class ChainSourceLocalIsometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original chain quotient preserves every pairwise source distance on a small ball away from the gluing faces.",
        H("Local source sheets of an original chain quotient"),
        Blocks(
            Paragraph(Text("Let I and J be types in independent universes and X an I-indexed family of extended metric spaces. Write A(X) for their original topological disjoint union. The datum G is the existing FiniteOrbitChainMetric.Datum: its source and target indices, closed gluing domains and ranges, and their partial isometries define the original finite chains and their cost infimum delta(G,a,b). A forward or inverse gluing step costs zero; a move within a piece costs its original extended distance.")),
            Paragraph(Text("Let Y be an extended metric space and q:A(X) to Y realize exactly delta on every pair of representatives. No surjectivity is required. For a in A(X), let i=first(a) and let center(a) be its point in X(i). Write OnBall(q,a,r) for the map from the original source ball eball(center(a),r) to Y which sends x to q(i,x). The radius r below is a nonnegative real, hence finite as an extended real.")),
            Describe.Lean(DescribeId.Create("original-chain-local-source-isometry"),
                DeclarationHandle.Create("D5/S3/Topology/ChainSourceLocalIsometry.original_chain_local_source_isometry"),
                H("All pairwise distances on a small source ball"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("U is open in the original disjoint union. The two exclusions range over every generator j and every point of its actual domain or range. Thus U avoids both endpoints of every permitted gluing step, including inverse steps and self-gluings. The conclusion needs no finiteness of I, J or the full equivalence classes, no compactness, and no finite-diameter condition.")),
                    Paragraph(Text("Pull U back to the selected source piece and choose a positive finite R whose ball lies in that pullback. Set r=R/4. A chain starting within r of the center and having cost less than 2r remains within 3r of that center. Prove this by induction on the actual chain: a paid move stays in the original piece and adds at most its cost, while a first forward or inverse gluing would have its current endpoint in U and in a forbidden domain or range. Such a step is impossible.")),
                    Paragraph(Text("For two points of the r-ball, their source distance is less than 2r. Any chain cheaper than that distance would satisfy the preceding confinement bound and would have cost at least the same source distance, a contradiction. This bounds the infimum over all original chains from below. The single paid source move bounds it from above, giving equality of every pairwise distance. No minimizing chain or bound on chain length is assumed.")))),
            Paragraph(Text("For the literal original quotient furnished by FiniteOrbitChainMetric.Datum.chain_metric_on_original_quotient, take its original projection as q and the metric supplied there. Whenever a source region satisfies these two generator exclusions, the theorem gives its small metric sheet in that same quotient, with the original quotient topology. This application adds no second quotient.")),
            Paragraph(Text("The result concerns source points away from every gluing domain and range. A point on a paired face or an edge does not satisfy this entrance. Such points require compatible charts across the participating pieces and their actual face transports. No global isometric embedding of a whole piece, edge-star cone chart, angle-sum assertion or hyperbolic manifold realization follows from this local statement alone.")))));

    private static Formula Statement()
    {
        var a=Id("a"); var b=Id("b"); var j=Id("j"); var y=Id("y"); var r=Id("r");
        var A=Call("A",Id("X")); var G=Id("G"); var U=Id("U"); var q=Id("q");
        var exact=All("a",A,All("b",A,Eq(Call("edist",App(q,a),App(q,b)),Call("delta",G,a,b))));
        var sources=All("j",Id("J"),All("y",Call("dom",G,j),
            Not(Call("Member",Call("Point",Call("src",G,j),y),U))));
        var targets=All("j",Id("J"),All("y",Call("ran",G,j),
            Not(Call("Member",Call("Point",Call("dst",G,j),y),U))));
        var result=All("q",new Formula.TypeArrow(A,Id("Y")),
            All("U",Call("Set",A),All("a",A,Implies(
                And(exact,Call("IsOpen",U),sources,targets,Call("Member",a,U)),
                Exists("r",Id("NNReal"),And(Lt(F.D(0),r),Call("Isometry",Call("OnBall",q,a,r))))))));
        result=All("Y",Id("Types"),F.Seq(F.OpenBracket,Call("EMetricSpace",Id("Y")),F.CloseBracket,F.Sp,result));
        result=All("G",Call("Datum",Id("I"),Id("J"),Id("X")),result);
        result=F.Seq(F.OpenBracket,All("i",Id("I"),Call("EMetricSpace",Call("X",Id("i")))),F.CloseBracket,F.Sp,result);
        return All("I",Id("Types"),All("J",Id("Types"),All("X",new Formula.TypeArrow(Id("I"),Id("Types")),result)));
    }
    private static Formula Id(string s)=>F.Id(s);
    private static Formula Call(string s,params Formula[] xs)=>new Formula.Apply(Id(s),[..xs]);
    private static Formula App(Formula f,params Formula[] xs)=>new Formula.Apply(f,[..xs]);
    private static Formula All(string s,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,b);
    private static Formula Exists(string s,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(s),t,b);
    private static Formula And(params Formula[] xs)
    {
        var r=xs[^1]; for(var i=xs.Length-2;i>=0;i--)r=new Formula.Logic(xs[i],FormulaLogicOperator.And,r);return r;
    }
    private static Formula Not(Formula a)=>F.Seq(F.Neg,F.Sp,a);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Lt(Formula a,Formula b)=>F.Seq(a,F.Sp,F.Lt,F.Sp,b);
    private static Formula Implies(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
}
