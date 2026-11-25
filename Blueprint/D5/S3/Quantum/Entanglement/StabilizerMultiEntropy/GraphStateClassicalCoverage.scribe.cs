using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;

internal sealed class GraphStateClassicalCoverageDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateClassicalCoverage.";
    private static readonly LibraryNoteRef Gce =
        LibraryNoteRef.Create("D5/L/QuantumStates/liu2025generalized");

    private static readonly LibraryNoteRef RankWidth =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/oum2005rankwidth");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Graph-state generalized concentratable entanglement has a universal classical hit-probability representation exactly at integer orders above one.",
        H("Integer orders and exact graph-state classical coverage"),
        Blocks(
            Describe.Lean(DescribeId.Create("graph-state-classical-coverage-iff"),
                DeclarationHandle.Create(Owner + "physical_graph_coverage_iff"),
                H("Universal classical hit law iff integer order"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(Gce),
                Blocks(
                    Paragraph(Text("A graph is any symmetric binary adjacency matrix with zero diagonal, including the graph on zero sites. "
                        + "The deficiency D(K,A,S) is one minus the arithmetic mean of the actual real power traces over the subsets of S, "
                        + "using the normalized reduced graph-state matrices. Equivalently it is (K - 1) times the GCE of S. "
                        + "A law p is nonnegative and normalized on binary words; Hit(S,p) is its mass on words nonzero on some site of S. "
                        + "One and the same law must work for all subsets S of the chosen graph.")),
                    Paragraph(Text("At order n + 1, sample n independent induced vertex subsets uniformly, form each induced graph's odd-degree set, "
                        + "and XOR those sets. Its exact linear-cut Fourier moments give the desired law. For a noninteger order, "
                        + "a binary projective incidence graph makes a signed marginal negative through the exact projective rank product. "
                        + "The theorem concerns universality over graph states. It does not say that every graph at a noninteger order fails."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("compact-projective-characteristic"),
                DeclarationHandle.Create(Owner + "compact_projective_characteristic"),
                H("The full-system Walsh factor of the compact projective graph"),
                StatementSource.FromAuthor(CompactStatement()), AssessedProvenance.FromRepo(RankWidth, Gce),
                Blocks(
                    Paragraph(Text("For each n, use every nonzero vector over the binary field in dimension n + 1 and one parallel copy "
                        + "of a basis vector. The fundamental graph of the resulting systematic chart has exactly 2^(n + 1) sites, "
                        + "including the basis sites but no ancillary coordinate or zero-vector sites. The observable is the normalized reduced "
                        + "graph-state matrix's actual real power trace at each subsystem. W is its alternating full-system sum; its candidate "
                        + "probability mass is W divided by 2 to the number of sites.")),
                    Paragraph(Text("Oum's Proposition 3.1 expresses a cut rank as the sum of the two restriction ranks minus total rank "
                        + "in this normalization. On a cut with neither side spanning, the residual is an exact product of the two rank defects in the powers. One cut side spans here because two proper binary subspaces cannot cover all points. "
                        + "Under this condition the cut moment is the sum of the two restriction-rank powers minus the full-rank power. "
                        + "Complementing the mask aligns the even full-system signs and the constant cancels. Grouping the two parallel "
                        + "copies gives the three weights -1, -1, +1, so their total agrees with a single copy. The resulting signed sum "
                        + "is the binary projective characteristic product, namely twice the product of (1 − 2^j/q) over 0 ≤ j ≤ n.")),
                    Paragraph(Text("Let q be 2^(K-1). For the graph of dimension m + 2, only the last product factor is negative when "
                        + "2^m < q < 2^(m+1). No nonnegative probability law can then reproduce the averaged trace deficiencies of "
                        + "this graph on every subset. This does not claim that every graph fails at noninteger order, or that this size "
                        + "is optimal for every band."))),
                DescribeRole.Theorem))));

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), domain, body);
    private static Formula All(string name, Formula domain, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        Bind(FormulaQuantifier.Exists, name, domain, body);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));

    private static Formula CompactStatement()
    {
        var k = F.Id("K");
        var n = F.Id("n");
        var m = F.Id("m");
        var q = Call("q", k);
        var nat = Seq(Mathbb, Grp(F.Id("N")));
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var factor = All("n", nat, Equal(Call("W", k, n), Call("ProjectiveFactor", q, n)));
        var band = All("m", nat, Implies(Call("OpenDyadicBand", q, m),
            Call("NoCommonHitLaw", k,
                new Formula.Binary(m, FormulaBinaryOperator.Add, Num(1)))));
        var consequence = new Formula.Logic(P(factor), FormulaLogicOperator.And, P(band));
        return Disp(All("K", real, Implies(
            new Formula.Relation(Num(1), FormulaRelationOperator.LessThan, k), consequence)));
    }

    private static Formula Statement()
    {
        var k = F.Id("K");
        var n = F.Id("n");
        var N = F.Id("N");
        var a = F.Id("A");
        var S = F.Id("S");
        var p = F.Id("p");
        var nat = Seq(Mathbb, Grp(F.Id("N")));
        var sites = Call("Fin", N);
        var laws = All("N", nat, All("A", Call("SimpleBinaryAdjacency", sites),
            Ex("p", Call("ProbabilityOnBinaryWords", sites),
                All("S", Call("Subsets", sites), Equal(Call("D", k, a, S), Call("Hit", S, p))))));
        var integer = Ex("n", nat, Equal(k, new Formula.Binary(n, FormulaBinaryOperator.Add, Num(1))));
        var iff = new Formula.Logic(P(laws), FormulaLogicOperator.Iff, P(integer));
        return Disp(All("K", Seq(Mathbb, Grp(F.Id("R"))), Implies(
            new Formula.Relation(Num(1), FormulaRelationOperator.LessThan, k), iff)));
    }
}
