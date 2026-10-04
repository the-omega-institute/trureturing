using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class CompleteStraightPathCountsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every fixed relative ordering, complete ordered deletion from the single parent blocker has at least one path at every depth. Complete counts and geometric-memory counts at every positive radius are bounded by three to the depth, including depth zero.",
        H("Straight continuations and finite path counts"),
        Blocks(
            Paragraph(Text("Let P be the singleton integer-grid blocker at (-1, 0). Ccomplete(a, n) is pathCount for completeStep, with the constant policy selecting a at every history and blocker set, depth n, empty initial history and initial blockers P. Cmemory(r, a, n) uses geometricStep r with exactly the same policy, depth, history and initial blockers. The six values of a are the six relative neighbor orderings; r is a natural-number retention radius.")),
            Describe.Lean(
                DescribeId.Create("hard-core-complete-straight-path-bounds"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/CompleteStraightPathCounts.complete_straight_path_bounds"),
                H("Positive complete counts and uniform upper bounds"),
                StatementSource.FromAuthor(BoundsFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The forward direction is (1, 0). If every recorded blocker has first coordinate at most zero, this direction is available. Every newly deleted point is either the current origin or a candidate neighbor, so its first coordinate is at most one, independently of the ordering. The forward recentering subtracts one from that coordinate. Thus the actual complete update preserves the weak left half-plane. Induction on depth retains the forward summand in the recursive path count, starting from P; at depth zero the count is one.")),
                    Paragraph(Text("The fixed-order block bound with zero full blocks bounds every positive-radius memory count by three to the depth. Complete-count domination by radius-one memory then supplies the complete upper bound. These are finite-depth integer bounds and do not assert any growth-rate limit or interchange of infima."))),
                DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula BoundsFormula()
    {
        Formula a = F.Id("a"), n = F.Id("n"), r = F.Id("r");
        Formula complete = Call("Ccomplete", a, n);
        Formula bound = new Formula.Power(D(3), n);
        Formula memory = All("r", Naturals(), new Formula.Logic(
            AtMost(D(1), r), FormulaLogicOperator.Implies,
            Parenthesized(AtMost(Call("Cmemory", r, a, n), bound))));
        return Disp(All("a", Call("Fin", D(6)), All("n", Naturals(),
            Parenthesized(And(AtMost(D(1), complete), And(AtMost(complete, bound), memory))))));
    }
}
