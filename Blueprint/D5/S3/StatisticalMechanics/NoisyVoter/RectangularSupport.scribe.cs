using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.NoisyVoter;

internal sealed class RectangularSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact finite graph-ball rectangles support the native joint opinion and source history.",
        H("Graph-ball support for the native voter history"),
        Blocks(
            Paragraph(Text("Let G be a connected locally finite undirected simple graph on an arbitrary vertex type V, let u be a root, and let N be any natural horizon. The finite enumeration K(G,u,N) is exactly the closed graph ball of radius N. Its construction starts with the singleton root and takes the union of the root with the radius-N balls at its actual neighbours. Shortest walks identify this finite enumeration with the displayed distance ball in the opening proof of Theorem 2.1 of the ancestral-collision source. The countable union of these balls is all of V.")),
            Paragraph(Text("The disjoint label type is the native Label V: an initial vertex or a pair consisting of a strictly positive natural birth time and a vertex. The set L(G,u,N) contains exactly the initial labels on K(G,u,N) and the fresh labels at times 1 through N on that same ball. The coordinate set rectangle(G,u,N) contains every initial opinion on the ball and every fresh opinion, refresh control and actual-neighbour choice at each time 1 through N on the ball. It is the complete rectangular set of the source, including coordinates not reached by a realized history. It includes no auxiliary time-zero coordinate.")),
            Paragraph(Text("RectangleState is the dependent vector of the native Value G c at every coordinate c in that rectangle, with the finite product measurable structure. restrictRectangle x u N w reads that vector from x at w. The native history x u N w records both nvm x s u w and source x s u w for all times s from zero through N. Each choice still takes values in the actual neighbour set of its vertex; a boundary choice may point outside the ball, but the causal recursion only consults it when the preceding time has a remaining distance budget.")),
            Describe.Lean(DescribeId.Create("voter-rectangular-support"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/NoisyVoter/RectangularSupport.rectangular_history_support"),
                H("Exact rectangular support and finite measurable joint reconstruction"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(
                    "D5/L/StatisticalMechanics/benjaminihelmantovzhukovskii2023noisyvoter")),
                Blocks(
                    Paragraph(Text("The statement holds for every sample type O, every connected locally finite G, every root and horizon, with a nonempty actual neighbour set at every vertex. Both label membership equivalences are exact; the positive natural type excludes a fresh birth at zero. The displayed decoder f is a single measurable function of the entire rectangular vector, valid for every coordinate assignment and every sample point. Every actual source in the joint history lies in L(G,u,N). The two finite sets are deterministic, and V is countable without a finite-graph hypothesis.")),
                    Paragraph(Text("The new induction uses the invariant dist(u,v)+n at most N. It proves that every recursively needed input for (v,n) is in the original rectangle and that its terminal label is in the original label set. The decoder restricts the rectangle to the existing historyInputs vector and directly applies finite_history_factorization from FiniteCausalInputs. No second proof of finite-input reconstruction or of cross-space law transport is introduced."))),
                DescribeRole.Theorem),
            Paragraph(Text("For Assumption 1.1, encode its initial opinions and strictly positive-time auxiliary coordinates as the native family x, and set N=t+d. Fill the unused time-zero fresh, refresh and choice slots arbitrarily. Every coordinate in the rectangle is initial or has strictly positive time, so the original measurability hypotheses make the rectangle vector measurable; composition with f gives measurable joint opinions and sources. Keep 0 < epsilon < 1 and the original mutual independence and marginal laws for initial and strictly positive-time coordinates: fair initial and fresh opinion coins, noisy refresh controls and uniform choices on actual neighbours. Apply the existing history_law_of_positive_coordinate_laws with that marginal family for cross-space transport. Neither a law nor independence nor measurability is required of the unused time-zero auxiliary slots. A native full-coordinate Model G P is a further application. The support argument itself is pathwise.")),
            Paragraph(Text("The horizon-zero case has K consisting only of u, L consisting only of the initial label at u, and the coordinate rectangle consisting only of the initial opinion at u. For t=0 and positive lag d the horizon is d and the repetition sum is empty. For general t and d every time i and i+d with 1 at most i at most t is within t+d. These readouts use the actual synchronous recursion and keep source equality distinct from colour agreement.")),
            Paragraph(Text("This supplies the exact graph-ball, label-support and finite measurable joint-reconstruction prerequisite in the opening proof of Theorem 2.1. It does not prove the subsequent variance identities, remainder formulas, equality criterion or unordered-pair grouping and multiplicity counting. These identities and counting statements require further arguments."))), []));

    private static Formula X(string n) => F.Id(n);
    private static Formula Named(string n) => Seq(Operatorname, Grp(X(n)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string n, params Formula[] args) => App(Named(n), args);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iffn(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Mem(Formula a, Formula b) => Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Leq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Eqn(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Ball() => Call("K", X("G"), X("u"), X("N"));
    private static Formula Labels() => Call("L", X("G"), X("u"), X("N"));
    private static Formula Coordinates() => Call("rectangle", X("G"), X("u"), X("N"));
    private static Formula Coord() => Call("Coord", X("V"));
    private static Formula Value() => Call("Value", X("G"), X("c"));
    private static Formula DepArr(string n, Formula t, Formula b) =>
        Seq(Open, X(n), Colon, t, Close, Sp, To, Sp, b);

    private static Formula Statement()
    {
        var ball = All("v", X("V"), Iffn(Mem(X("v"), Ball()), Leq(Call("dist", X("G"), X("u"), X("v")), X("N"))));
        var initial = All("v", X("V"), Iffn(Mem(Call("inl", X("v")), Labels()), Mem(X("v"), Ball())));
        var fresh = All("n", Named("PNat"), All("v", X("V"),
            Iffn(Mem(Call("inr", Seq(Open, X("n"), Comma, X("v"), Close)), Labels()),
                And(Leq(Call("val", X("n")), X("N")), Mem(X("v"), Ball())))));
        var positive = All("c", Coord(), Imp(Mem(X("c"), Coordinates()), Call("positive", X("c"))));
        var horizon = Call("Fin", Seq(X("N"), Plus, D(1)));
        var output = Arr(horizon, Seq(Named("Bool"), Times, Call("Label", X("V"))));
        var state = Call("RectangleState", X("G"), X("u"), X("N"));
        var fact = Eqn(Call("history", X("x"), X("u"), X("N"), X("w")),
            App(X("f"), Call("restrictRectangle", X("x"), X("u"), X("N"), X("w"))));
        var support = All("s", horizon, Mem(Call("source", X("x"), Call("val", X("s")), X("u"), X("w")), Labels()));
        var assignment = DepArr("c", Coord(), Arr(X("O"), Value()));
        var reconstruction = Ex("f", Arr(state, output), And(Call("Measurable", X("f")),
            All("x", assignment, All("w", X("O"), And(fact, support)))));
        var result = And(ball, And(Call("Countable", X("V")),
            And(initial, And(fresh, And(positive, reconstruction)))));
        var neighbours = All("v", X("V"), Ex("z", X("V"), Call("Adj", X("G"), X("v"), X("z"))));
        var body = Imp(Call("Connected", X("G")), Imp(neighbours,
            All("u", X("V"), All("N", Nat(), result))));
        return Disp(All("V", Named("Type"), All("O", Named("Type"),
            All("G", Call("SimpleGraph", X("V")),
                Seq(OpenBracket, Call("LocallyFinite", X("G")), CloseBracket, Sp, body)))));
    }
}
