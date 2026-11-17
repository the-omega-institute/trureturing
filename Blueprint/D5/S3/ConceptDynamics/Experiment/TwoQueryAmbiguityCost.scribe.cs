using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class TwoQueryAmbiguityCostDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Experiment/TwoQueryAmbiguityCost.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let C be a finite nonempty candidate set, Q a nonempty query type, and Y(q) an arbitrary dependent response type. A deterministic policy may use the entire dependent history, repeat queries, and stop at different depths on different candidates. Each query costs one observation. All states are sampled uniformly from C.", H("Uniform Mean Cost from Two-Query Ambiguity"), Blocks(
            Paragraph(Text("Let C be a finite nonempty candidate set, Q a nonempty query type, and Y(q) an arbitrary dependent response type. A deterministic policy may use the entire dependent history, repeat queries, and stop at different depths on different candidates. Each query costs one observation. All states are sampled uniformly from C.")),
            Describe.Lean(DescribeId.Create("first-branch-cost"), DeclarationHandle.Create(Prefix + "first_branch_cost"),
                H("The Actual First Branch Costs at Least 2m+r"), StatementSource.FromAuthor(Disp(Le(Add(Call("mul",D(2),F.Id("m")),F.Id("r")),Call("branchCost",F.Id("q"),F.Id("y"))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each realized first answer y assume its actual fibre has m members with m at least two. For every possible second query z assume at least r members have a distinct partner in that same first fibre with the same z answer. Trace injectivity forces a query at the root and in each first branch. A partnered candidate cannot stop after two observations: its partner would produce the same complete trace. Summing the pointwise lower costs 2 plus the indicator of this paired set gives at least 2m+r. The second query is extracted from the supplied tree and can depend on y."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tree-two-query-cost"), DeclarationHandle.Create(Prefix + "tree_two_query_cost"),
                H("Uniform Mean Lower Bound for Every Exact Tree"), StatementSource.FromAuthor(Disp(Le(Add(D(2),Div(F.Id("r"),F.Id("m"))),Call("uniformMeanCost",F.Id("C"),F.Id("p"))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume every realized first fibre has size m at least two, and for all first queries, realized answers, and second queries, the paired set has at least r members, with r at most m. Partition C over only the realized answers, so neither the ambient query nor response alphabet needs a Fintype. The actual root query yields C.card=m times the number of its realized answers; summing the branch bound and dividing by the positive carrier cardinal gives mean at least 2+r/m. Nonempty Q prevents vacuous fibre assumptions on a singleton carrier."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("history-two-query-cost"), DeclarationHandle.Create(Prefix + "history_two_query_cost"),
                H("Transfer to Every Terminating Exact History Policy"), StatementSource.FromAuthor(Disp(Le(Add(D(2),Div(F.Id("r"),F.Id("m"))),Call("uniformMeanLength",F.Id("C"),F.Id("tr"))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every C member supply an actual completed execution of the policy, with full trace tr(C) and terminal label lab(C). Pointwise termination suffices; no common fuel bound is assumed. A decoder of those labels must equal C on every legal candidate. FiniteHistoryCanonicalTree derives a common unfolding depth and preserves every query, dependent response, terminal history, label, and trace length without pruning repeats. Applying tree_two_query_cost and transporting the actual lengths gives the same mean lower bound. The conclusion also identifies the actual first query, the exact first-fibre partition, all branch lower sums, and their total."))), DescribeRole.Theorem),
            Paragraph(Text("The displayed formulas abbreviate the complete hypotheses stated in each paragraph; the bound is over actual finite candidate traces, not a bit cost or running-time claim. The reusable result adds a branchwise ambiguity estimate to the existing finite-history bridge; it imports that bridge directly and does not duplicate it. No probability law beyond the stated uniform prior, noise model, randomized-policy claim, or external literature novelty is asserted.")))));

    private static Formula Call(string n, params Formula[] xs) => xs.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(n))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(n)), [.. xs]);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
}
