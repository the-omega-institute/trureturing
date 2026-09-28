using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class TernaryTreeBudgetObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A ternary partial table has tree support and exact one-sided costs two, yet no deterministic simultaneous protocol can use at most two reachable messages on each side.",
        H("A Ternary Tree Obstruction to Two Messages per Side"),
        Blocks(
            Definition("task", "Task", "Partial ternary tasks", null,
                "For arbitrary types X and Y, Task(X,Y) is X -> Y -> Option(Fin 3). "
                + "The output type O = Fin 3 consists of 0, 1, 2. A value some(o) prescribes output o; "
                + "none marks an illegal input pair and is not an output. Write D(t) for the set "
                + "of pairs (x,y) with t(x,y) different from none, and write t transpose for the "
                + "table (y,x) |-> t(x,y)."),
            Definition("table", "table", "The actual table", TableFormula(),
                "Here X = Y = O = Fin 3, and F denotes table. Rows and columns are ordered 0,1,2. "
                + "An asterisk denotes none; each numeral denotes some of that output. The five "
                + "legal entries are F(0,0)=0, F(1,0)=1, F(1,1)=0, F(2,1)=1, F(2,2)=2. "
                + "All three output labels occur, and every row and column is active."),
            Definition("support", "support", "The actual simple bipartite support", null,
                "The vertices of support(t) are the disjoint union X + Y. Its adjacency relates "
                + "inl(x) and inr(y), in either order, exactly when t(x,y) is not none. There "
                + "are no edges within either side and no loops. Thus each legal pair gives one "
                + "unordered simple edge. Below G means support(F), E(G) its unordered edge set, "
                + "and V its full vertex type Fin 3 + Fin 3."),
            Definition("left-conflict", "conflictLeft", "Original row conflicts", null,
                "Vertices x and u in conflictLeft(t) are adjacent exactly when there exist "
                + "y in Y and a,b in O such that t(x,y)=some(a), t(u,y)=some(b), and a differs "
                + "from b. The shared column and both legal entries belong to the original table. "
                + "Write GA for conflictLeft(F)."),
            Definition("right-conflict", "conflictRight", "Original column conflicts", null,
                "conflictRight(t) is conflictLeft(t transpose). Thus y and v are adjacent "
                + "exactly when one original row x has two legal entries t(x,y)=some(a) and "
                + "t(x,v)=some(b) with a different from b. Write GB for conflictRight(F)."),
            Definition("budget", "HasBudget", "All ambient simultaneous protocols", BudgetFormula(),
                "For natural p,q, HasBudget(t,p,q) quantifies over arbitrary ambient types A,B, "
                + "separate encoders alpha:X->A and beta:Y->B, and a total decoder delta:A->B->O. "
                + "Neither alphabet is required to be finite. The charged quantities are "
                + "Nat.card(Set.range alpha) and Nat.card(Set.range beta). For this table both "
                + "ranges are finite because the inputs are finite, even when the ambient "
                + "alphabets are infinite. The vertical bars in the displayed definitions "
                + "denote these natural cardinalities. Correctness is required for every x,y,o with "
                + "t(x,y)=some(o), and imposes no condition on illegal pairs. The decoder "
                + "receives only the two messages. The ordered budgets count reachable symbols."),
            Definition("one-sided-budget", "HasOriginalBudget", "The original one-sided budget", OriginalBudgetFormula(),
                "HasOriginalBudget(t,p) quantifies over an arbitrary ambient type A, an encoder "
                + "alpha:X->A and a total decoder d:A->Y->O. At most p values of alpha are "
                + "reachable, and d(alpha(x),y)=o for every legal entry t(x,y)=some(o). "
                + "This decoder retains the other party's original input y. Transposing t "
                + "gives the corresponding right-sided definition."),
            Definition("cost", "originalCost", "Exact original input costs", CostFormula(),
                "originalCost(t) is the infimum in the natural numbers of the budgets p "
                + "satisfying HasOriginalBudget(t,p). For F and its transpose the proof "
                + "exhibits budget two and proves that every feasible budget is at least two; "
                + "the infimum is therefore an attained minimum. These are actual one-sided "
                + "protocol costs, as well as the chromatic numbers computed below."),
            Definition("path-index", "pathIndex", "The six-vertex path order", PathFormula(),
                "pathIndex sends inl(0), inr(0), inl(1), inr(1), inl(2), inr(2) to "
                + "0,1,2,3,4,5 respectively in Fin 6. Hence its path order is exactly "
                + "x0-y0-x1-y1-x2-y2."),
            Describe.Lean(
                DescribeId.Create("ternary-actual-properties"), DeclarationHandle.Create(Prefix + "ActualProperties"),
                H("The complete seventeen-clause positive certificate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("ActualProperties is the conjunction of the following seventeen clauses, "
                        + "in this order. Every clause concerns the same table F. Cardinalities are finite; "
                        + "the rank expression is evaluated in the integers.")),
                    Paragraph(Text("1. The output type Fin 3 has cardinality 3.")),
                    Paragraph(Text("2. For every o in Fin 3, there exist x,y in Fin 3 with F(x,y)=some(o).")),
                    Paragraph(Text("3. For every x in Fin 3, there exist y,o in Fin 3 with F(x,y)=some(o).")),
                    Paragraph(Text("4. For every y in Fin 3, there exist x,o in Fin 3 with F(x,y)=some(o).")),
                    Paragraph(Text("5. The set D(F) of legal input pairs has cardinality 5.")),
                    Paragraph(Text("6. The actual unordered simple edge set E(G) has cardinality 5.")),
                    Paragraph(Text("7. The full vertex type V = Fin 3 + Fin 3 has cardinality 6; clauses 3 and 4 make all six vertices active.")),
                    Paragraph(Text("8. pathIndex:V->Fin 6 is bijective.")),
                    Paragraph(Text("9. For every v,w in V, G.Adj(v,w) holds if and only if "
                        + "pathIndex(v).val+1=pathIndex(w).val or pathIndex(w).val+1=pathIndex(v).val.")),
                    Paragraph(Text("10. G is a tree: it is connected and acyclic.")),
                    Paragraph(Text("11. The integer expression |D(F)|-|Fin 3|-|Fin 3|+1 equals 0. "
                        + "This is 5-3-3+1, without truncated natural subtraction.")),
                    Paragraph(Text("12. GA equals pathGraph 3, with exactly the edges 0-1 and 1-2.")),
                    Paragraph(Text("13. GB equals pathGraph 3, with exactly the edges 0-1 and 1-2.")),
                    Paragraph(Text("14. The chromatic number of GA equals 2.")),
                    Paragraph(Text("15. The chromatic number of GB equals 2.")),
                    Paragraph(Text("16. originalCost(F) equals 2.")),
                    Paragraph(Text("17. originalCost(F transpose) equals 2."))), DescribeRole.Definition),
            Definition("claim", "claim", "The proposed ternary implication", ClaimFormula(),
                "claim is the closed proposition ActualProperties implies HasBudget(F,2,2). "
                + "The antecedent contains all seventeen positive properties. Its consequent "
                + "asserts existence of a correct protocol over some arbitrary ambient alphabets, "
                + "with at most two reachable messages on each side."),
            Describe.Lean(
                DescribeId.Create("ternary-tree-budget-obstruction"), DeclarationHandle.Create(Prefix + "result"),
                H("The positive certificate holds and every two-by-two protocol fails"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The theorem is the negation of the entire proposed implication. "
                        + "Equivalently, ActualProperties holds and HasBudget(F,2,2) is false. "
                        + "The proof constructs every positive clause and excludes existence of "
                        + "any correct protocol, for all choices of A,B,alpha,beta,delta in the "
                        + "definition above.")),
                    Paragraph(Text("Legal pairs map bijectively to unordered edges by "
                        + "(x,y) |-> {inl(x),inr(y)}. The five actual edges connect all six "
                        + "vertices in the stated order; connectedness and the edge count "
                        + "give a tree. Checking the original entries gives both exact "
                        + "conflict paths and hence both chromatic numbers two.")),
                    Paragraph(Text("For each one-sided protocol use the encoder 010 into Fin 2. "
                        + "For F, the total decoder has rows (0,1,2) and (1,0,0), indexed "
                        + "by the message and columns indexed by the original y. For F transpose, "
                        + "the total decoder has rows (0,1,2) and (0,0,1), with columns indexed "
                        + "by the original x. All five required equations hold in each case. "
                        + "Conversely, the entries (0,0),(1,0) force two distinct left messages; "
                        + "the entries (1,0),(1,1) force two distinct right messages. Thus "
                        + "every one-sided budget is at least two, proving the exact minima.")),
                    Paragraph(Text("Now suppose an arbitrary ambient protocol is correct on "
                        + "the five legal entries. The pairs (0,0),(1,0) force alpha(0) "
                        + "different from alpha(1), and (1,1),(2,1) force alpha(1) different "
                        + "from alpha(2). The pairs (1,0),(1,1) force beta(0) different "
                        + "from beta(1), and (2,1),(2,2) force beta(1) different from beta(2). "
                        + "If either encoder also separated its endpoints, it would be "
                        + "injective on Fin 3 and its reachable image would have cardinality "
                        + "three. The two-message bounds therefore force alpha(0)=alpha(2) "
                        + "and beta(0)=beta(2). The legal inputs (0,0) and (2,2) then give "
                        + "the same message pair, which the total decoder would have to send "
                        + "both to 0 and to 2. This contradiction applies to all ambient "
                        + "types, rather than only a fixed two-symbol decoder enumeration.")),
                    Paragraph(Text("The conclusion concerns this three-output task. It shows "
                        + "that exact original costs two cannot replace the Boolean output "
                        + "hypothesis in a forest guarantee. The Boolean forest theorem "
                        + "remains valid; no conclusion about the unresolved uniform Boolean "
                        + "region at cycle rank three follows from this example."))), DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string declaration, string title, Formula? formula, string prose) =>
        Describe.Lean(DescribeId.Create("ternary-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula App(string name, params Formula[] arguments) => new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Apply(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Par(Formula formula) => Seq(Open, formula, Close);
    private static Formula Card(Formula formula) => Seq(Bar, formula, Bar);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string v, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula Ex(string v, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), domain, body);
    private static Formula Ex(Formula v, Formula domain, Formula body) =>
        Seq(Exists, Sp, v, Colon, domain, Comma, Sp, body);
    private static Formula Both(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Equivalence(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Par(b));
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    private static Formula TableFormula() => Disp(Seq(F.Id("F"), Eq,
        Begin, Grp(F.Id("pmatrix")), D(0), Amp, Star, Amp, Star, RowBreak,
        D(1), Amp, D(0), Amp, Star, RowBreak, Star, Amp, D(1), Amp, D(2),
        End, Grp(F.Id("pmatrix"))));

    private static Formula Protocol(Formula table, Formula p, Formula q, bool oneSided)
    {
        Formula x = F.Id("x"), y = F.Id("y"), o = F.Id("o"), a = Alpha, b = Beta, d = DeltaLower;
        Formula correctness = All("x", F.Id("X"), All("y", F.Id("Y"), All("o", F.Id("O"),
            Imp(Equal(Apply(table, x, y), App("some", o)), Equal(Apply(d, Apply(a, x), oneSided ? y : Apply(b, y)), o)))));
        Formula bounds = AtMost(Card(App("range", a)), p);
        if (!oneSided) bounds = Both(bounds, AtMost(Card(App("range", b)), q));
        Formula body = Ex(d, Arrow(F.Id("A"), Arrow(oneSided ? F.Id("Y") : F.Id("B"), F.Id("O"))),
            Par(Both(bounds, correctness)));
        if (!oneSided) body = Ex(b, Arrow(F.Id("Y"), F.Id("B")), body);
        body = Ex(a, Arrow(F.Id("X"), F.Id("A")), body);
        if (!oneSided) body = Ex("B", Named("Type"), body);
        return Ex("A", Named("Type"), body);
    }

    private static Formula BudgetFormula() => Disp(Equivalence(App("HasBudget", F.Id("t"), F.Id("p"), F.Id("q")),
        Protocol(F.Id("t"), F.Id("p"), F.Id("q"), false)));
    private static Formula OriginalBudgetFormula() => Disp(Equivalence(App("HasOriginalBudget", F.Id("t"), F.Id("p")),
        Protocol(F.Id("t"), F.Id("p"), D(0), true)));
    private static Formula CostFormula() => Disp(Equal(App("originalCost", F.Id("t")),
        App("sInf", Seq(OpenBrace, F.Id("p"), Colon, Mathbb, Grp(F.Id("N")), Mid, Sp,
            App("HasOriginalBudget", F.Id("t"), F.Id("p")), CloseBrace))));
    private static Formula PathFormula() => Disp(Seq(
        App("pathIndex", App("inl", F.Id("i"))), Eq, D(2), F.Id("i"), Comma, Quad, Sp,
        App("pathIndex", App("inr", F.Id("j"))), Eq, D(2), F.Id("j"), Plus, D(1)));
    private static Formula ClaimFormula() => Disp(Equivalence(Named("claim"),
        Imp(Named("ActualProperties"), App("HasBudget", F.Id("F"), D(2), D(2)))));
    private static Formula ResultFormula() => Disp(new Formula.Not(Par(
        Imp(Named("ActualProperties"), App("HasBudget", F.Id("F"), D(2), D(2))))));
}
