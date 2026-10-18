using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Pressure;
internal sealed class StationaryVariationalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stationary pressure with zero masses and zero probabilities", H("Stationary pressure with zero masses and zero probabilities"), Blocks(
        Paragraph(Text("X is an arbitrary finite type with decidable equality. G is strongly connected Prop-valued edge support with an actual edge; costs are arbitrary real functions and temperature is positive. A StationaryPair contains nonnegative normalized pi, a nonnegative row-stochastic Q supported on the original G.edge, and the exact column balance pi Q = pi. Both pi and Q may have zero entries. Entropy is minus the full finite sum pi(i)Q(i,j)log Q(i,j), with zero products contributing zero. The objective is the actual mean c minus temperature times this entropy.")),
        Describe.Lean(DescribeId.Create("actual-graph-result"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Pressure/StationaryVariational.variational_minimum"),
            H("Stationary pressure with zero masses and zero probabilities"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                "D5/L/GraphInvariants/friedlandgaubert2019spectral")),
            Blocks(Paragraph(Text("On a nonzero Q entry, support gives a positive Qstar entry and permits expanding log Qstar = -c/temperature + log r(j) - log r(i) - log root. At a zero Q entry the weighted term is exactly zero. Row normalization and column stationarity cancel the arbitrary potential log r. The exact identity is temperature*weightedKL = objective + temperature*log root for every StationaryPair. Apply GrandmotherTheorem.kl_divergence_nonneg directly to full rows, with absolute continuity supplied by graph support. At an actual stationary law of Qstar, every row KL is zero. Hence the minimum is attained on the same actual W."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Family(Formula body) => All("X", Call("FiniteDecidableType"),All("G", Call("Network",F.Id("X")),
        All("c",Call("RealEdgeCosts",F.Id("X")),All("temperature",Call("Real"),body))));
    private static Formula Statement()
    {
        Formula g=F.Id("G"), c=F.Id("c"), t=F.Id("temperature"), p=F.Id("p"), q=F.Id("q");
        Formula pressure=Call("neg",Mul(t,Call("log",Call("root",Call("perron",g,c,t)))));
        Formula minimum=And(Eq(Call("Q",p),Call("Qstar",g,c,t)),And(
            Eq(Call("objective",p,c,t),pressure),All("q",Call("StationaryPair",g),Le(pressure,Call("objective",q,c,t)))));
        Formula witness=new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create("p"),Call("StationaryPair",g),minimum);
        return Family(new Formula.Logic(new Formula.Relation(D(0),FormulaRelationOperator.LessThan,t),FormulaLogicOperator.Implies,witness));
    }
}
