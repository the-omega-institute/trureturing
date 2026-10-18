using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Pressure;
internal sealed class PeriodicGrowthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Periodic-safe every-state transfer growth", H("Periodic-safe every-state transfer growth"), Blocks(
        Paragraph(Text("X is an arbitrary finite type with decidable equality. G is strongly connected Prop-valued edge support with an actual edge; costs are arbitrary real functions and temperature is real. The abbreviation growthQuotient denotes n mapped to log((W^n times the all-ones column)(i))/n. The observable is (W^n times the all-ones column)(i), for every starting state i and n. It sums over terminal states. The proof does not replace it by a fixed-terminal matrix entry and does not assume primitive convergence. If m and M bound the actual positive right eigenvector, the exact factors are r(i)/M below and r(i)/m above, multiplied by root^n.")),
        Describe.Lean(DescribeId.Create("actual-graph-result"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Pressure/PeriodicGrowth.weighted_growth"),
            H("Periodic-safe every-state transfer growth"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                "D5/L/GraphInvariants/friedlandgaubert2019spectral")),
            Blocks(Paragraph(Text("Inductively transport the actual eigenrelation through each matrix power. Nonnegativity compares the weighted row sums against m and M. Both constant multiples are positive, so logarithms and division by n for n at least one give a squeeze around log root. Finite extrema supply m>0 and M>0, and the additive constants divided by n tend to zero. At zero supported costs W is the actual counting adjacency, and the complex spectral-radius equality gives its logarithmic growth. An explicit bijection to a finite type of unrestricted directed walks is not yet delivered. The original minimum-cycle-mean, maximum-outdegree bracket, and zero-temperature limit remain unpaid; none is inferred from these components."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Family(Formula body) => All("X", Call("FiniteDecidableType"),All("G", Call("Network",F.Id("X")),
        All("c",Call("RealEdgeCosts",F.Id("X")),All("temperature",Call("Real"),body))));
    private static Formula Statement() => Family(All("i",F.Id("X"),Call("Tendsto",
        Call("growthQuotient",F.Id("G"),F.Id("c"),F.Id("temperature"),F.Id("i")),
        Call("atTop"),Call("nhds",Call("log",Call("root",Call("perron",F.Id("G"),F.Id("c"),F.Id("temperature"))))))));
}
