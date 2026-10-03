using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Decision;

internal sealed class ExactRealProbeCostsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact real probes flip a hidden Boolean label at exactly one real coordinate.",
        H("Exact Real Probe Costs"),
        Blocks(Describe.Lean(
            DescribeId.Create("exact-real-probe-costs"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Decision/ExactRealProbeCosts.result"),
            H("Sound certificates"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("A source is a pair (x,b) with x in the closed unit interval "
                    + "and b Boolean. Querying a returns b unless a=x, when it returns the "
                    + "opposite bit. A history keeps the exact parameter and response of "
                    + "each query; its cost is the number of different parameters.")),
                Paragraph(Text("Consistency means that every recorded response agrees with "
                    + "the source. Soundness means that every consistent source has the "
                    + "reported task bit. Every source has a sound certificate using two "
                    + "different parameters, and no compatible sound history uses fewer.")),
                Paragraph(Text("The two certificate parameters may depend on the specified "
                    + "source. Choose two distinct parameters different from x: their "
                    + "responses agree with b, whereas an opposite-label source would "
                    + "have to coincide with both parameters."))),
            DescribeRole.Theorem))));

    private static Formula App(string name, params Formula[] args) => Call(name, args);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Implies(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Forall(string name, string type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), F.Id(type), body);
    private static Formula Exists(string name, string type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), F.Id(type), body);

    private static Formula Statement()
    {
        var s = F.Id("s");
        var h = F.Id("h");
        var b = App("label", s);
        var compatible = App("Consistent", h, s);
        var sound = App("Sound", h, b);
        var cost = App("queryCount", h);
        return Disp(Forall("s", "Source", And(
            Forall("h", "History", Implies(compatible, Implies(sound,
                new Formula.Relation(Num(2), FormulaRelationOperator.LessThanOrEqual, cost)))),
            Exists("h", "History", And(compatible, And(sound, Equal(cost, Num(2))))))));
    }
}
