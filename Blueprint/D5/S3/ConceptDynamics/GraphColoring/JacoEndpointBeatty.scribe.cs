using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class JacoEndpointBeattyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual recursively constructed Jaco endpoints are golden Beatty endpoints at every natural index.",
        H("The recursive Jaco endpoint law"),
        Blocks(
            Node("recurrence", "endpoint_recurrence", "The source recurrence",
                "At every positive n, the endpoint is twice n minus the number of positive earlier endpoints reaching n. Prefix agreement of the existing array construction identifies every stored entry with its original endpoint; this connects the array implementation to the source recurrence.",
                Disp(Bound("n", Naturals(), Implies(LessEqual(D(1), N),
                    Equal(Call("jacoRight", N), Subtract(Multiply(D(2), N),
                        Call("card", SetBuilder(Typed(F.Id("i"), Naturals()),
                            And(LessEqual(D(1), F.Id("i")), And(Less(F.Id("i"), N),
                                LessEqual(N, Call("jacoRight", F.Id("i"))))))))))))),
            Describe.Lean(DescribeId.Create("beatty-outdegree"),
                DeclarationHandle.Create(Prefix + "beattyOut"), H("The Beatty outdegree candidate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a natural index n, beattyOut n is the natural floor of (n+1) divided by the golden ratio. Its identification with an actual graph quantity is proved through the recursive endpoint law."))), DescribeRole.Definition),
            Node("bounds", "beatty_bounds", "Positive outdegree bounds",
                "For every positive n, the candidate lies between one and n, using the golden ratio strictly between one and two.",
                Disp(Bound("n", Naturals(), Implies(LessEqual(D(1), N),
                    And(LessEqual(D(1), B(N)), LessEqual(B(N), N)))))),
            Node("threshold", "beatty_threshold", "Invert the endpoint threshold",
                "For arbitrary natural n and i, the candidate endpoint at i reaches n exactly when i is at least beattyOut n. The golden-ratio floor identity and irrationality account for the strict boundary; no equality case is discarded without proof.",
                Disp(Bound("n", Naturals(), Bound("i", Naturals(),
                    Iff(LessEqual(N, Add(F.Id("i"), B(F.Id("i")))), LessEqual(B(N), F.Id("i"))))))),
            Node("endpoint", "endpoint_eq_beatty", "The actual all-order endpoint",
                "Strong induction replaces each earlier recursive endpoint by its proved Beatty value. The incoming indices become exactly the interval from beattyOut n through n-1, whose cardinality is n minus beattyOut n. Substituting this count in the source recurrence gives the endpoint law. Index zero remains only the unused table entry.",
                Disp(Bound("n", Naturals(), Equal(Call("jacoRight", N), Add(N, B(N)))))))));

    private static Formula N => F.Id("n");
    private static Formula B(Formula n) => Call("beattyOut", n);
    private static DocumentBlock Node(string id, string declaration, string title, string prose, Formula formula) =>
        Describe.Lean(DescribeId.Create("jaco-endpoint-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Naturals() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Bound(string n, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LessEqual(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Typed(Formula a, Formula b) => Seq(a, Colon, Sp, b);
    private static Formula SetBuilder(Formula a, Formula b) => Seq(OpenBrace, a, Sp, Mid, Sp, b, CloseBrace);
}
