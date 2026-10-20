using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class OrderedMatchingIntervalsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Label transport across closed matching intervals.",
        H("Label transport across closed matching intervals"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("interval"),
                DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingIntervals.closed_interval_gap"),
                H("Label transport across closed matching intervals"), StatementSource.FromAuthor(FormulaDsl.Disp(All("L", V("Type"), All("n", V("Natural"), All("M", Call("NCMatching", V("n")), All("y", Call("Function", Call("Fin", Add(V("n"), Num(1))), V("L")), All("l", Call("Fin", Add(V("n"), Num(1))), All("r", Call("Fin", Add(V("n"), Num(1))), Implies(Call("Compatible", V("M"), V("y")), Implies(AtMost(V("l"), V("r")), Implies(Call("IntervalClosed", V("M"), V("l"), V("r")), Equal(Call("Apply", V("y"), V("l")), Call("Apply", V("y"), V("r")))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A partner-closed interval has equal boundary labels under every compatible labelling. Strong induction removes its first matched block and retains a closed suffix. The interval may contain any number of nested or disjoint arcs, and zero length is included."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => Id(name);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}
