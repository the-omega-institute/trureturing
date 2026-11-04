using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class TreeMarkovStabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/TreeMarkovStability.";
    private static Formula I(string s) => F.Id(s);
    private static Formula Rel(Formula a, Formula op, Formula b) => Seq(a, Sp, op, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Paren(a), Sp, Land, Sp, Paren(b));
    private static Formula All(Formula variables, Formula body) => Seq(Forall, Sp, variables, Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => Seq(Paren(a), Sp, Rightarrow, Sp, Paren(b));
    private static Formula Paren(Formula a) => Seq(Open, a, Close);
    private static Formula SumAt(string index, Formula f) => Seq(Sum, Underscore, Grp(I(index)), Sp, f);
    private static Formula TV(Formula a, Formula b) => Call("TV", a, b);
    private static Formula Node(string family, Formula i) => Call("node", I(family), i);
    private static Formula Edge(string family, Formula i, Formula j) => Call("edge", I(family), i, j);
    private static Formula Norm(Formula p) => And(All(I("x"), Rel(D(0), Le, Call("eval", p, I("x")))),
        Equal(SumAt("x", Call("eval", p, I("x"))), D(1)));
    private static Formula Nodes(Formula p, string family) => All(I("i"),
        Equal(Call("pushforward", Call("coordinate", I("i")), p), Node(family, I("i"))));
    private static Formula Edges(Formula p, string family) => All(Seq(I("i"), Comma, I("j")),
        Imp(Call("Adj", I("G"), I("i"), I("j")),
            Equal(Call("pushforward", Call("coordinates", I("i"), I("j")), p),
                Edge(family, I("i"), I("j")))));
    private static Formula NodeCharge() => Call("nodeBudget", I("G"),
        Seq(I("i"), Mapsto, TV(Node("F", I("i")), Node("H", I("i")))));
    private static Formula Kernels() => All(Seq(I("t"), Colon, Call("TreeOrder", I("G")), Comma,
            I("K"), Colon, Call("KernelFamily", I("X"))),
        Imp(All(Seq(I("i"), Comma, I("j")), Imp(Call("Adj", I("G"), I("i"), I("j")),
            All(Seq(I("a"), Comma, I("b")),
                Imp(Rel(Call("eval", Node("F", I("i")), I("a")), Neq, D(0)),
                    Equal(Call("K", I("i"), I("j"), I("a"), I("b")),
                        Call("quotient", Call("eval", Edge("F", I("i"), I("j")), I("a"), I("b")),
                            Call("eval", Node("F", I("i")), I("a")))))))),
            Equal(Call("factorMass", I("t"), I("F"), I("K")), I("P"))));

    private static Formula Result()
    {
        Formula p = I("P"), q = I("Q"), e = Call("edgeBudget", I("F"), I("H"));
        Formula equalNodes = All(I("i"), Equal(Node("F", I("i")), Node("H", I("i"))));
        Formula bounds = And(Rel(TV(p, q), Le, Call("min", D(1), Add(e, NodeCharge()))),
            Imp(equalNodes, Rel(TV(p, q), Le, Call("min", D(1), e))));
        Formula conclusion = And(Norm(p), And(Norm(q), And(Nodes(p, "F"), And(Nodes(q, "H"),
            And(Edges(p, "F"), And(Edges(q, "H"), And(bounds, And(
                All(Seq(I("root"), Colon, I("V")), Seq(Exists, Sp, I("t"), Colon,
                    Call("TreeOrder", I("G")), Comma, Sp, Equal(Call("root", I("t")), I("root")))),
                Kernels()))))))));
        Formula premises = And(Call("IsTree", I("G")), And(Rel(D(2), Le, Call("card", I("V"))),
            And(Equal(p, Call("markovLaw", I("G"), I("F"))),
                Equal(q, Call("markovLaw", I("G"), I("H"))))));
        return All(Seq(I("V"), Colon, I("FiniteType"), Comma, I("G"), Colon, Call("SimpleGraph", I("V")),
            Comma, I("X"), Colon, Seq(I("V"), Sp, To, Sp, I("FiniteType")), Comma,
            I("F"), Comma, I("H"), Colon, Call("Family", I("G"), I("X")), Comma,
            p, Comma, q, Colon, Call("Mass", Call("Configurations", I("X")))), Imp(premises, conclusion));
    }

    private static Formula Sharpness()
    {
        Formula p = Call("markovLaw", I("G"), I("F"));
        Formula q = Call("markovLaw", I("G"), I("H"));
        Formula assumptions = And(Call("IsTree", I("G")),
            And(Rel(D(2), Le, Call("card", I("V"))),
                All(I("i"), Equal(Node("F", I("i")), Node("H", I("i"))))));
        Formula universal = All(Seq(I("V"), Colon, I("FiniteType"), Comma,
            I("G"), Colon, Call("SimpleGraph", I("V")), Comma,
            I("X"), Colon, Seq(I("V"), Sp, To, Sp, I("FiniteType")), Comma,
            I("F"), Comma, I("H"), Colon, Call("Family", I("G"), I("X"))),
            Imp(assumptions, Rel(TV(p, q), Le, Call("min", D(1),
                Multiply(I("c"), Call("edgeBudget", I("F"), I("H")))))));
        return Seq(Neg, Paren(Seq(Exists, Sp, I("c"), Colon, Mathbb, Grp(I("R")), Comma,
            And(Rel(I("c"), Lt, D(1)), universal))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized Markov laws on arbitrary finite trees satisfy degree-weighted total-variation bounds with sharp edge coefficient one.",
        H("Actual Finite-Tree Markov Stability"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-finite-tree-stability"),
                DeclarationHandle.Create(Prefix + "actual_tree_stability"),
                H("Normalization, marginals, stability and conditional-row independence"),
                StatementSource.FromAuthor(Disp(Result())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A Family on G and X assigns to each vertex i a nonnegative normalized real mass " +
                        "on the finite state space X(i), and to each actual edge ij a nonnegative coupling with exactly " +
                        "those two marginals. Reversing an edge transposes its coupling. The coordinate at a shared " +
                        "vertex is the same variable in every incident edge; equality of unrelated marginal values " +
                        "is not an identification of their sources. Nonedge coupling entries are unused.")),
                    Paragraph(Text("A TreeOrder removes leaves until one actual edge remains. Every finite graph tree " +
                        "with at least two vertices has such an order at every prescribed root. Its joint mass starts with that edge coupling " +
                        "and adds each removed leaf through the quotient of its coupling by the parent marginal. " +
                        "A zero-mass parent row is completed with the child's normalized node law. The displayed " +
                        "P and Q are the resulting markovLaw masses; finite types may differ from vertex to vertex.")),
                    Paragraph(Text("Both masses are nonnegative, have total one, and push forward to every prescribed " +
                        "node and oriented edge law. Here TV is half the sum of absolute mass differences. " +
                        "edgeBudget is half the sum of oriented-edge TVs, hence counts every undirected edge once. " +
                        "nodeBudget(G,d) is the sum over vertices i of (degree(i)-1)d(i), with real subtraction. " +
                        "The two displayed minima include the probability bound one.")),
                    Paragraph(Text("The leaf extension inequality adds the edge TV and the parent-node TV. Deleting " +
                        "a leaf reduces precisely the corresponding degree charge, so induction gives the full bound. " +
                        "Equal node laws remove all node charges. No positive lower bound on node masses is needed.")),
                    Paragraph(Text("KernelFamily(X) consists of real functions K(i,j,a,b). The quotient condition in " +
                        "the last conjunct fixes K only at nonzero parent masses; the values at zero mass may be " +
                        "arbitrary, so in particular every normalized probability completion is allowed. factorMass " +
                        "starts with a root node and its first conditional factor, followed by the leaf factors. " +
                        "The equality holds for every TreeOrder, including both orientations of its root edge. " +
                        "A zero node marginal forces the entire configuration fiber to have zero mass. On the " +
                        "remaining configurations, the square of the density is the product of squared node masses " +
                        "times the orientation-independent product of edge-to-node ratios. Nonnegativity then " +
                        "gives equality across all orders. Thus the Markov factorization class has a unique law; " +
                        "arbitrary joint laws with the same low-order marginals are not asserted to be unique."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("universal-sharp-edge-coefficient"),
                DeclarationHandle.Create(Prefix + "edge_coefficient_one_sharp"), H("Universal sharpness"),
                StatementSource.FromAuthor(Disp(Sharpness())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("SmallerEdgeCoefficient is the closed claim that there exists a real c<1 " +
                    "such that, for every finite tree with at least two vertices, every family of finite node spaces " +
                    "and every two consistent normalized families F,H with equal node laws, their actual markovLaw " +
                    "TV is at most min(1,c*edgeBudget(F,H)). Its negation excludes every smaller universal coefficient. " +
                    "On the two-vertex Bool tree, the diagonal and antidiagonal couplings have the same uniform " +
                    "node laws. Their actual constructed joint laws have TV one and edgeBudget one. Applying the " +
                    "proposed universal inequality to this member forces 1<=c, contradicting c<1."))),
                DescribeRole.Theorem))));
}
