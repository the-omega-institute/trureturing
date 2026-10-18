using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Pressure;
internal sealed class CyclePressureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimum directed-cycle mean and zero-temperature pressure", H("Minimum directed-cycle mean and zero-temperature pressure"), Blocks(
        Paragraph(Text("X ranges over arbitrary finite types with decidable equality; Network X means precisely the original Prop-valued strongly connected support with an actual edge, and RealEdgeCosts X means arbitrary X-to-X real costs. SupportClosedWalk(G,x) is the actual supportGraph.Walk x x; IsSimpleCycle uses the existing cycle predicate. minimumCycleMean is the mean of the constructed attaining simple cycle, and maxOutdegree is the attained maximum cardinality of actual successor subtypes. realNat casts this degree to the reals. pressureFunction(G,c) is temperature mapped to minus temperature times log of the constructed actual Perron root. nhdsRight(0) denotes the right-hand neighborhood filter at zero. No PF data, chosen cycle, potential, or pressure bracket occurs as a supplied premise.")),
        Paragraph(Text("SupportEdge is precisely the subtype of ordered pairs satisfying the original Prop-valued support. supportGraph uses their original source and target. Strong connectivity and an actual edge supply a nonempty closed walk. The existing simple-cycle reduction supplies a simple cycle. Its existing length bound makes the set of actual mean costs finite. minimumCycle chooses a minimizing actual cycle from that nonempty finite set. outdegree counts the actual successor subtype, and maxOutdegree is the maximum of these cardinalities. The result includes an attaining cycle, minimality against all nonempty closed walks including repetitions, an attaining maximum degree, the exact temperature bracket and the right-hand zero-temperature limit.")),
        Describe.Lean(DescribeId.Create("actual-support-law"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Pressure/CyclePressure.cycle_pressure_laws"),
            H("Minimum directed-cycle mean and zero-temperature pressure"), StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                "D5/L/GraphInvariants/friedlandgaubert2019spectral")),
            Blocks(Paragraph(Text("Use the existing cycle reduction and one-sided potential suppliers directly, with weight=-cost and level=-minimumCycleMean. The resulting potential satisfies -cost+phi(source)-phi(target)<=-minimumCycleMean. For each positive temperature use z=exp(-phi/temperature). Each actual supported matrix term satisfies W(i,j)z(j)<=exp(-minimum/temperature)z(i); summation counts actual successors. At a vertex maximizing the actual positive Perron-vector ratio r/z, its eigenrelation gives the upper Perron bound with the actual maximum outdegree. Multiply Perron row inequalities along the actual minimizing cycle; its positive right-vector factor cancels because the walk is closed, giving the lower bound. Real logarithms give minimum-temperature*log(maximumDegree)<=-temperature*log(root)<=minimum. The squeeze yields the right-hand zero-temperature limit. The construction uses the same original graph, costs, matrix and actual Perron vector throughout."))), DescribeRole.Theorem))));

    private static Formula Call(string n, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(n))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(n)), [.. args]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);

    private static Formula Statement()
    {
        Formula x=F.Id("x"), w=F.Id("w"), g=F.Id("G"), c=F.Id("c"), t=F.Id("temperature");
        Formula m=Call("minimumCycleMean",g,c), d=Call("maxOutdegree",g);
        Formula pressure=Call("neg",Mul(t,Call("log",Call("root",Call("perron",g,c,t)))));
        Formula attaining=Ex("x",F.Id("X"),Ex("w",Call("SupportClosedWalk",g,x),
            And(Call("IsSimpleCycle",w),Eq(Call("cycleMean",g,c,w),m))));
        Formula allClosed=All("x",F.Id("X"),All("w",Call("SupportClosedWalk",g,x),
            Imp(Lt(D(0),Call("length",w)),Le(m,Call("cycleMean",g,c,w)))));
        Formula degree=And(Ex("x",F.Id("X"),Eq(Call("outdegree",g,x),d)),Le(D(1),d));
        Formula bracket=All("temperature",Call("Real"),Imp(Lt(D(0),t),
            And(Le(Sub(m,Mul(t,Call("log",Call("realNat",d)))),pressure),Le(pressure,m))));
        Formula limit=Call("Tendsto",Call("pressureFunction",g,c),Call("nhdsRight",D(0)),Call("nhds",m));
        Formula body=And(attaining,And(allClosed,And(degree,And(bracket,limit))));
        return All("X",Call("FiniteDecidableType"),All("G",Call("Network",F.Id("X")),
            All("c",Call("RealEdgeCosts",F.Id("X")),body)));
    }
}
