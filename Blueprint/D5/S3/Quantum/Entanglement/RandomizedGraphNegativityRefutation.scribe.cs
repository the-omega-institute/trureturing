using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class RandomizedGraphNegativityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/wu2014randomized");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Wu, Rossi, Kampermann, Severini, Kwek, Macchiavello and Bruss (arXiv:1403.3828, Section V) ask whether the negativity of a randomized graph state, across any bipartition, increases monotonically with the probability p that each edge is present. It does not: for the complete bipartite graph K_(3,3) and the bipartition into its two parts, the negativity is larger than 1/2 at p = 97/100 and at most 1/2 at p = 1.",
        H("The negativity of randomized graph states is not monotone"),
        Blocks(
            Node("cz", "Controlled-Z phases", CzFormula(),
                "The n qubits are indexed by Fin(n) and the computational basis by the maps x from Fin(n) to Bool, with true read as 1 and false as 0. The controlled-Z gate on the edge {a, b} is diagonal in this basis, with entry (-1)^(x(a) x(b)) at the basis state x.",
                "czPhase", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("plus", "The product state", PlusFormula(),
                "The state |+>^n has every computational-basis amplitude equal to 2^(-n/2).",
                "plusState", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("graph", "Graph states", GraphFormula(),
                "The graph state of an edge set F is the product of the controlled-Z gates of its edges applied to |+>^n. These gates are diagonal, so the amplitude at x is the product of their phases at x times the amplitude of |+>^n.",
                "graphState", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rg", "Randomized graph states", RgFormula(),
                "Each edge of G is present independently with probability p. The randomized graph state is the mixture, over the subsets F of the edge set of G, of the projections onto the graph states of F, with weights p^|F| (1 - p)^(|E(G)| - |F|).",
                "rgState", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("neg", "Negativity", NegFormula(),
                "The negativity across the bipartition A versus its complement is (||rho^Gamma_A|| - 1)/2. The partial transposition rho^Gamma_A is the existing transposePart: its entry at (x, y) is the entry of rho at the row label with A part from y and remaining part from x, and the column label with A part from x and remaining part from y. The trace norm ||X|| = Re Tr sqrt(X^* X) is that of the existing finite trace-distance module.",
                "negativity", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The question", ClaimFormula(),
                "The paper reports monotone negativity for the complete graphs and the star graphs with at most 4 vertices and states that it is an open question whether the monotonic behaviour of the negativity in p is a common feature of all randomized graph states, the negativity being evaluated with respect to all bipartitions. The displayed statement reads the question as a universal statement over finite simple graphs on Fin(n), subsets A of the vertices and 0 <= p <= q <= 1.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("k33", "The graph K_(3,3)", K33Formula(),
                "The complete bipartite graph on Fin(6) whose parts are the even and the odd vertices.",
                "k33", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("part", "One part of K_(3,3)", PartFormula(),
                "The part A is the set of even vertices.",
                "partA", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "The answer is negative", Disp(new Formula.Not(F.Id("claim"))),
                "Expanding the product over the edges, the entry of the randomized state of a graph at (x, y) is 2^(-n) times the product over its edges of p c + (1 - p), where c = 1 if x and y have equal products x(a) x(b) on the edge and c = -1 otherwise. For K_(3,3) with the bipartition into its parts A = {0, 2, 4} and B = {1, 3, 5}, the entries of the partial transpose X_p are therefore (1 - 2p)^d / 64, with d the number of edges on which the two exchanged labels disagree. At p = 1 let u_00 and u_11 be the indicators of even and odd parity on A, times 1 and times the sign (-1)^|x_B| on B respectively, and let w and v be the difference and the sum of the indicator of even parity on A times (-1)^|x_B| and the indicator of odd parity on A. Entry by entry, X_1 + (1/128) w w^T equals (1/64)(u_00 u_00^T + u_11 u_11^T) + (1/128) v v^T. Both sides are sums of positive semidefinite rank-one terms, so by the triangle inequality ||X_1|| is at most the trace of the right side plus the trace of (1/128) w w^T, that is 3/2 + 1/2 = 2, and the negativity at p = 1 is at most 1/2. At p = 97/100, fourteen pairwise orthogonal integer vectors u_j of length 64 give the projection P = sum_j u_j u_j^T / |u_j|^2 and the unitary I - 2P; the trace norm is at least Re Tr((I - 2P) X_(97/100)) = 1 - 2 sum_j u_j^T X u_j / |u_j|^2, and this exact rational number is larger than 2. So the negativity at p = 97/100 exceeds 1/2, which contradicts monotonicity between p = 97/100 and q = 1.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wu-2014-randomized-graph-negativity-monotonicity"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("rgn-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula EqTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula LeTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Member(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Frac(Formula top, Formula bottom) => new Formula.Fraction(top, bottom);
    private static Formula Pow(Formula b, Formula e) => new Formula.Power(b, e);
    private static Formula NumberSet(Formula name) => Seq(Mathbb, Grp(name));
    private static Formula Nat() => NumberSet(F.Id("N"));
    private static Formula Real() => NumberSet(F.Id("R"));
    private static Formula Fin(Formula n) => Call(F.Id("Fin"), n);
    private static Formula Qubits(Formula n) => Call(F.Id("Qubits"), n);
    private static Formula VertexSets(Formula n) => Call(F.Id("Finset"), Fin(n));
    private static Formula EdgeSets(Formula n) => Call(F.Id("Finset"), Call(F.Id("Sym2"), Fin(n)));
    private static Formula Matrices(Formula n) =>
        Seq(NumberSet(F.Id("C")), Caret, Grp(Qubits(n), Sp, F.Times, Sp, Qubits(n)));
    private static Formula ProdOver(Formula index, Formula body) =>
        Seq(Prod, Underscore, Grp(index), Sp, body);
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(Sum, Underscore, Grp(index), Sp, body);
    private static Formula Card(Formula set) => Call(F.Id("card"), set);

    private static Formula CzFormula()
    {
        Formula n = F.Id("n"), a = F.Id("a"), b = F.Id("b"), x = F.Id("x");
        Formula phase = Pow(Parenthesized(Seq(Minus, D(1))), Mul(Call(x, a), Call(x, b)));
        return Disp(All(n, Nat(), All(a, Fin(n), All(b, Fin(n), All(x, Qubits(n),
            EqTo(Call(F.Id("czPhase"), Call(F.Id("s"), a, b), x), phase))))));
    }

    private static Formula PlusFormula()
    {
        Formula n = F.Id("n"), x = F.Id("x");
        Formula amplitude = Pow(Parenthesized(Frac(D(1), Seq(Sqrt, Grp(D(2))))), n);
        return Disp(All(n, Nat(), All(x, Qubits(n),
            EqTo(Call(F.Id("plusState"), n, x), amplitude))));
    }

    private static Formula GraphFormula()
    {
        Formula n = F.Id("n"), f = F.Id("F"), e = F.Id("e"), x = F.Id("x");
        Formula phases = ProdOver(Member(e, f), Call(F.Id("czPhase"), e, x));
        Formula value = Mul(Parenthesized(phases), Call(F.Id("plusState"), n, x));
        return Disp(All(n, Nat(), All(f, EdgeSets(n), All(x, Qubits(n),
            EqTo(Call(F.Id("graphState"), f, x), value)))));
    }

    private static Formula RgFormula()
    {
        Formula n = F.Id("n"), g = F.Id("G"), p = F.Id("p"), f = F.Id("F");
        Formula edges = Call(F.Id("edgeFinset"), g);
        Formula state = Call(F.Id("graphState"), f);
        Formula weight = Mul(Pow(p, Card(f)),
            Pow(Parenthesized(Sub(D(1), p)), Card(Seq(edges, Sp, Setminus, Sp, f))));
        Formula projection = Call(F.Id("vecMulVec"), state, Call(F.Id("star"), state));
        Formula value = SumOver(Seq(f, Sp, Subseteq, Sp, edges),
            Mul(weight, projection));
        return Disp(All(n, Nat(), All(g, Call(F.Id("SimpleGraph"), Fin(n)), All(p, Real(),
            EqTo(Call(F.Id("rgState"), g, p), value)))));
    }

    private static Formula NegFormula()
    {
        Formula n = F.Id("n"), a = F.Id("A"), rho = Rho;
        Formula value = Frac(Sub(Call(F.Id("traceNorm"), Call(F.Id("transposePart"), a, rho)),
            D(1)), D(2));
        return Disp(All(n, Nat(), All(a, VertexSets(n), All(rho, Matrices(n),
            EqTo(Call(F.Id("negativity"), a, rho), value)))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), g = F.Id("G"), a = F.Id("A"), p = F.Id("p"), q = F.Id("q");
        Formula left = Call(F.Id("negativity"), a, Call(F.Id("rgState"), g, p));
        Formula right = Call(F.Id("negativity"), a, Call(F.Id("rgState"), g, q));
        Formula body = Imp(LeTo(D(0), p), Imp(LeTo(p, q), Imp(LeTo(q, D(1)), LeTo(left, right))));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            All(n, Nat(), All(g, Call(F.Id("SimpleGraph"), Fin(n)), All(a, VertexSets(n),
                All(p, Real(), All(q, Real(), body)))))));
    }

    private static Formula K33Formula()
    {
        Formula a = F.Id("a"), b = F.Id("b");
        Formula parity = Seq(Neg, Sp, Parenthesized(Seq(a, Equiv, Sp, b, Pmod, Grp(D(2)))));
        return Disp(All(a, Fin(D(6)), All(b, Fin(D(6)),
            Logic(Call(F.Id("Adj"), F.Id("k33"), a, b), FormulaLogicOperator.Iff, parity))));
    }

    private static Formula PartFormula() =>
        Disp(EqTo(F.Id("partA"),
            Seq(Esc, OpenBrace, D(0), Comma, Sp, D(2), Comma, Sp, D(4), Esc, CloseBrace)));
}
