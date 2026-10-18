using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Pressure;
internal sealed class WeightedWalksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unrestricted weighted walks and counting entropy", H("Unrestricted weighted walks and counting entropy"), Blocks(
        Paragraph(Text("X ranges over arbitrary finite types with decidable equality; Network X means precisely the original Prop-valued strongly connected support with an actual edge, and RealEdgeCosts X means arbitrary X-to-X real costs. Temperature is any real number in this law. matrixPowerOne(G,c,temperature,n,x) means ((W^n) times the all-ones column)(x). walkGrowthQuotient is n mapped to log(walkSum(G,c,temperature,n,x))/n; countGrowthQuotient is n mapped to log(Nat.card(Walks(G,n,x)))/n. ZeroSupportedCosts means c(i,j)=0 on every actual supported edge. realNatCard casts that exact cardinality to the reals, and complexSpectralRadius is spectralRadius over the complex numbers of the actual adjacency matrix embedded into the complex matrices. Nat includes zero. All walks retain repeated vertices and edges.")),
        Paragraph(Text("Walks n x recursively chooses one actual supported successor at each step. Its zero-length case has one inhabitant. There is no visited-set restriction, so loops, repetitions, returns and periodic cycles are included. walkBoltzmann is the product of exp(-cost/temperature) along the chosen edges. The finite sum is exactly the original matrix power applied to the all-ones column, for every natural n and state x. Zero supported costs make every weight one, yielding Nat.card of this same walk type. The growth limit uses the existing actual Perron vector and actual complex adjacency radius; no aperiodicity or row-normalized reference is introduced.")),
        Paragraph(Text("For a positive temperature tau, let lambda and r be the constructed positive Perron root and right vector of the actual exponential adjacency W. Define Qstar(i,j)=W(i,j)r(j)/(lambda r(i)). The eigenrelation makes each row sum one; Qstar is nonnegative and is positive exactly on the original support. Applying FiniteStochasticMixing.stationary_distribution_exists to this finite row-stochastic matrix gives a stationary probability pi and an attainer (pi,Qstar), without any aperiodicity assumption.")),
        Paragraph(Text("The stationary variational consequence ranges over every graph-supported pair (pi,Q), with pi and Q nonnegative, sum pi=1, every row sum Q=1, and sum_i pi(i)Q(i,j)=pi(j). Set E=sum_ij pi(i)Q(i,j)c(i,j), h=-sum_ij pi(i)Q(i,j)log Q(i,j), and K=sum_i pi(i) KL(Q(i,.) || Qstar(i,.)). Zero entries and zero stationary masses are allowed. A zero Q term contributes zero; a nonzero Q term lies on the graph support and hence has strictly positive Qstar, so its logarithm quotient is legitimate.")),
        Paragraph(Text("Expand log Qstar(i,j)=-c(i,j)/tau+log r(j)-log lambda-log r(i). Multiplying by tau*pi(i)Q(i,j) and summing gives tau*K=E-tau*h+tau*log lambda: the potential sum involving log r(i)-log r(j) vanishes by row normalization and column stationarity, and the total edge mass is one. The existing full-row kl_divergence_nonneg makes K nonnegative, including zero entries and zero stationary masses. At the stationary Doob pair K=0. Consequently the minimum over all these stationary pairs is attained and equals -tau*log lambda. The finite stationary-existence and KL theorems thus give the attained variational identity on the original support.")),
        Paragraph(Text("For every start i and every n including zero, if m and M are positive lower and upper bounds for r, the actual matrix row sum lies between (r(i)/M)*lambda^n and (r(i)/m)*lambda^n. The proof applies the pinned Module.End.HasEigenvector.pow_apply result to Perron.eigen through Matrix.toLin'_pow and Matrix.toLin'_apply, with the positive Perron vector supplying the nonzero eigenvector witness, and uses nonnegative matrix powers. Taking logarithms for n>=1 and squeezing after division by n gives the same growth rate at every start, including periodic supports. At zero supported costs W is the unnormalized counting adjacency. The unrestricted-walk cardinality therefore has entropy log of its actual complex spectral radius.")),
        Paragraph(Text("The cycle comparison combines with these identities to give finite-graph pressure laws for arbitrary real supported costs, all positive temperatures, the stationary minimum with zeros, every unrestricted walk length and starting vertex, counting entropy, the constructed minimum directed-cycle mean and maximum outdegree bracket, and the right-hand zero-temperature limit.")),
        Describe.Lean(DescribeId.Create("actual-support-law"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Pressure/WeightedWalks.unrestricted_walk_laws"),
            H("Unrestricted weighted walks and counting entropy"), StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                "D5/L/GraphInvariants/friedlandgaubert2019spectral")),
            Blocks(Paragraph(Text("Partition the successor-walk sigma type by its first actual successor and distribute the finite weighted sums. Induction on n identifies the result with W^n times the all-ones column. Apply the existing periodic growth theorem to this equality. For zero costs, induction makes each Boltzmann product one and the sum is the cardinality; apply the existing zero-cost actual adjacency spectral-radius identity."))), DescribeRole.Theorem))));

    private static Formula Call(string n, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(n))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(n)), [.. args]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Statement()
    {
        Formula x=F.Id("x"), n=F.Id("n"), g=F.Id("G"), c=F.Id("c"), t=F.Id("temperature");
        Formula sum=Call("walkSum",g,c,t,n,x);
        Formula enumeration=All("n",Call("Nat"),All("x",F.Id("X"),Eq(sum,Call("matrixPowerOne",g,c,t,n,x))));
        Formula growth=All("x",F.Id("X"),Call("Tendsto",Call("walkGrowthQuotient",g,c,t,x),Call("atTop"),
            Call("nhds",Call("log",Call("root",Call("perron",g,c,t))))));
        Formula zero=Imp(Call("ZeroSupportedCosts",g,c),All("n",Call("Nat"),All("x",F.Id("X"),
            Eq(sum,Call("realNatCard",Call("Walks",g,n,x))))));
        Formula counting=All("x",F.Id("X"),Call("Tendsto",Call("countGrowthQuotient",g,x),Call("atTop"),
            Call("nhds",Call("log",Call("toReal",Call("complexSpectralRadius",Call("adjacency",g)))))));
        Formula body=And(enumeration,And(growth,And(zero,counting)));
        return All("X",Call("FiniteDecidableType"),All("G",Call("Network",F.Id("X")),
            All("c",Call("RealEdgeCosts",F.Id("X")),All("temperature",Call("Real"),body))));
    }
}
