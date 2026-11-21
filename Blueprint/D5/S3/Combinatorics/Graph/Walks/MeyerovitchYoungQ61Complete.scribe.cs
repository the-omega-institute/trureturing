using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class MeyerovitchYoungQ61CompleteDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete min-plus matrices preserve the finite-horizon value of primitive graph games.",
        H("The complete matrix reduction for Meyerovitch–Young Question 6.1"),
        Blocks(
            Paragraph(Text("In the game of Meyerovitch and Young, Alice chooses a legal edge word of a fixed length, and Bob minimizes its paired edge payoff over all Bob walks of that length. Both endpoints of each walk are free. The reduction applies to arbitrary finite nonempty primitive directed multigraphs and to costs in any linearly ordered commutative ring, including the field in Question 6.1. https://arxiv.org/html/2603.21449v1#S6.Thmlemma1")),
            Describe.Lean(
                DescribeId.Create("finite-horizon-reduction"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61Complete.finite_horizon_reduction"),
                H("Exact word scores and the original maximizing walks"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The matrix family has one matrix per Alice edge, with rows and columns indexed by Bob's vertex and a freely chosen Alice vertex. The free-endpoint matrix score is the minimum entry sum over complete vertex walks. Adding the boundary charge gives the original Bob minimum minus C times the number of incompatible joins. The charge is zero for the empty word and for a singleton Alice vertex set, and is C otherwise.")),
                    Paragraph(Text("For each Bob response in the lifted graph, setting the exit register to the current Alice edge's target saves an exit charge larger than the entry penalty it can affect at the next step. The initial register is free, so its minimum contribution gives precisely the common boundary charge. A legal original Bob walk lifts with those registers and attains the penalized score.")),
                    Paragraph(Text("Fix a connector of common length for every pair of Alice vertices. Scan the Alice word and copy each compatible edge. At an incompatible join replace a connector-length block with a walk to the original terminal vertex of the block. Replace a final short suffix with a walk of its own length. Each replacement begins at an original incompatible join. Against the same Bob response its loss is bounded by the connector length times the payoff range. Choosing C above that bound makes any illegal word strictly worse than its repair.")),
                    Paragraph(Text("For each ordered pair of lifted Bob vertices, minimize over its parallel edges. Give missing pairs a common cost above the largest original cost plus the connector length minus one times the cost range. Any minimum using a missing pair admits a strictly cheaper connector-length replacement with the same endpoints. For a shorter horizon, any original Bob walk of that length gives a strictly cheaper response because endpoints are free."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matrix-minimum-spec"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61Complete.matrixMinimum_spec"),
                H("Attainment and lower bound for the matrix minimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a matrix family over a linearly ordered commutative ring on a finite nonempty vertex set, each word has a complete walk whose entry sum is the matrix minimum. The walk has the length of the word, and the same minimum bounds the entry sum of every complete walk of that length from below."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula v = F.Id("V"), e = F.Id("E"), w = F.Id("W"), f = F.Id("F"), k = F.Id("K");
        Formula x = F.Id("X"), y = F.Id("Y"), p = F.Id("p"), a = F.Id("a"), n = F.Id("n");
        Formula dx = F.Id("dX"), dy = F.Id("dY"), hx = F.Id("hX"), hy = F.Id("hY");
        Formula matrix = F.Id("A"), c = F.Id("C"), m = F.Id("m"), value = F.Id("z");
        Formula word = Call("List", e), nat = Call("Nat");
        Formula pair = Seq(Open, w, Sp, Times, Sp, v, Close);
        Formula length = Call("length", a);
        Formula legal = Call("Legal", x, a);
        Formula original = Call("freeMinimum", y, dy, hy, p, a);
        Formula complete = Call("matrixMinimum", matrix, a);
        Formula lengthN = Rel(length, FormulaRelationOperator.Equal, n);
        Formula boundary = Call("boundary", v, c, n);
        Formula originalSet = SetOf(value, k, Some("a", word,
            And(lengthN, And(legal, Rel(original, FormulaRelationOperator.Equal, value)))));
        Formula completeSet = SetOf(value, k, Some("a", word,
            And(lengthN, Rel(complete, FormulaRelationOperator.Equal, value))));
        Formula adjusted = Bin(complete, FormulaBinaryOperator.Add, boundary);
        Formula sameMaximizers = All("a", word, Logic(lengthN, FormulaLogicOperator.Implies,
            Logic(Rel(adjusted, FormulaRelationOperator.Equal, m), FormulaLogicOperator.Iff,
                And(legal, Rel(original, FormulaRelationOperator.Equal, m)))));
        Formula horizon = All("n", nat, Some("m", k,
            And(Call("IsGreatest", originalSet, m),
                And(Call("IsGreatest", completeSet, Bin(m, FormulaBinaryOperator.Subtract, boundary)),
                    sameMaximizers))));
        Formula charge = Bin(c, FormulaBinaryOperator.Multiply, Call("badJoins", x, a));
        Formula scores = All("a", word,
            Rel(Bin(complete, FormulaBinaryOperator.Add, Call("boundary", v, c, length)),
                FormulaRelationOperator.Equal, Bin(original, FormulaBinaryOperator.Subtract, charge)));
        Formula result = Some("A", Arrow(e, Call("Matrix", pair, pair, k)), Some("C", k,
            And(Rel(D(0), FormulaRelationOperator.LessThan, c), And(scores, horizon))));
        Formula inputs = All("X", Call("EdgeGraph", v, e), All("Y", Call("EdgeGraph", w, f),
            All("dX", nat, All("dY", nat,
                All("hX", Call("ConnectsAt", x, Bin(dx, FormulaBinaryOperator.Add, D(1))),
                All("hY", Call("ConnectsAt", y, Bin(dy, FormulaBinaryOperator.Add, D(1))),
                All("p", Arrow(e, Arrow(f, k)), result)))))));
        Formula instances = Seq(Inst("Finite", v), Inst("Nonempty", v), Inst("Finite", e),
            Inst("Finite", w), Inst("Nonempty", w), Inst("Finite", f), Inst("CommRing", k),
            Inst("LinearOrder", k), Inst("IsStrictOrderedRing", k), inputs);
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. new[] { "V", "E", "W", "F", "K" }.Select(name =>
                new Formula.BoundVariable(FormulaIdentifier.Create(name), Call("Type")))], instances));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Bin(Formula a, FormulaBinaryOperator op, Formula b) => new Formula.Binary(a, op, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), op, Seq(Open, b, Close));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula SetOf(Formula a, Formula type, Formula body) =>
        Seq(OpenBrace, a, Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Inst(string name, Formula type) => Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
}
