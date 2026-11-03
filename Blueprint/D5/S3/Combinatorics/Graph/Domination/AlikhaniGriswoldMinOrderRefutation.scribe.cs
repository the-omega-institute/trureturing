using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class AlikhaniGriswoldMinOrderRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/AlikhaniGriswoldMinOrderRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Zeros/alikhanigriswold2026integerdominationroots");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A connected 21-vertex ordinary-domination witness at minus four refutes the complete order-33 minimality claim.",
        H("The order-33 integer domination-root minimality claim"),
        Blocks(
            Paragraph(Text("Alikhani and Griswold, arXiv:2608.00109v1, Section 4 item 2 asks whether n=33 is the minimal order of a finite simple connected graph whose ordinary domination polynomial vanishes at -4. The formal claim retains both attainment at order 33 and nonvanishing at every positive order below 33.")),
            Node("claim", "The complete order-33 minimality claim", "claim", DescribeRole.Definition,
                Eq(Typed(X("claim"), X("Prop")), P(ClaimBody())),
                AssessedProvenance.FromLiterature(Source),
                "The first conjunct asserts an order-33 connected graph with ordinary domination evaluation zero at -4. The second conjunct asserts that every positive n below 33 and every connected graph on Fin n has nonzero ordinary domination evaluation. Dominating subsets are counted once and need not be connected."),
            Node("result", "A 21-vertex counterexample refutes minimality", "result", DescribeRole.Theorem,
                new Formula.Not(P(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                "The explicit 21-vertex graph has the 25 listed undirected edges. Its core is induced on 0 through 6, with branches 7 through 12 and 13 through 20 rooted at 7 and 13 and incident on core sets {0} and {0,3,4}. The accepted ordinary decomposition gives message pairs (-1024,972) and (-3328,6912); the same supplied decomposition and exact table cancellation yield evaluation zero at -4. The graph is connected by the displayed paths from vertex 0. Since 1 <= 21 < 33, this contradicts the lower-bound conjunct and answers the source question negatively. No claim that 21 is minimal is made.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("alikhani-griswold-2026-minus-four-minimum-order"),
                    ResolutionKind.Refuted)),
            Paragraph(Text("The result is a literal refutation of the complete source claim; it does not assert that 21 is the least counterexample order."))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, DescribeRole role,
        Formula formula, AssessedProvenance provenance, string prose,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Graph(Formula n) => Call("SimpleGraph", Call("Fin", n));
    private static Formula P(Formula body) => Seq(Open, body, Close);
    private static Formula Typed(Formula value, Formula type) => P(Seq(value, Colon, Sp, type));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(P(a), FormulaLogicOperator.And, P(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula DominationSum(Formula graph) =>
        Seq(F.Sum, Sp, Grp(Seq(X("S"), Sp, InMacro, Sp, Call("domSets", graph))), Sp,
            new Formula.Power(P(Seq(Minus, D(4))), Call("card", X("S"))));
    private static Formula ClaimBody()
    {
        var n = X("n");
        var graph = X("G");
        var attainment = Some("G", Graph(Num(33)),
            And(Call("Connected", graph), Eq(DominationSum(graph), D(0))));
        var lower = All("n", Nat(),
            Imp(Le(D(1), n),
                Imp(Lt(n, Num(33)),
                    All("G", Graph(n),
                        Imp(Call("Connected", graph),
                            Ne(DominationSum(graph), D(0)))))));
        return And(attainment, lower);
    }
}
