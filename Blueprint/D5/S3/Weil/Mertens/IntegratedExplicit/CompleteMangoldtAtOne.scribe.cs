using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class CompleteMangoldtAtOneDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtAtOne.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The removable singularity of the complete Mangoldt transform at one",
        H("Filling the complete Mangoldt transform at one"),
        Blocks(
            Describe.Lean(DescribeId.Create("completed"), DeclarationHandle.Create(Module + "completed"),
                H("The completed transform"), StatementSource.FromAuthor(F.Disp(Definition())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Write T for the explicit complete Mangoldt transform, h for the entire normalized zeta "
                    + "function, and A for its logarithmic derivative. Away from 1, h(s)=(s−1)ζ(s). "
                    + "At 1 its value is 1 and its derivative is Euler's constant γ. "
                    + "Thus A(1)=γ. The completed transform is denoted by F."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniqueness"), DeclarationHandle.Create(Module + "completed_analytic_unique"),
                H("Analyticity and uniqueness of the fill"), StatementSource.FromAuthor(F.Disp(Claim())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The original rational expression on the punctured neighborhood of 1 equals "
                        + "[1+γ−(A(s)−A(1))/(s−1)]/s. The term 1/(s−1) in the negative logarithmic "
                        + "derivative cancels the double pole after these fractions are combined. "
                        + "The divided difference extends analytically with value A′(1).")),
                    Paragraph(Text("At every other nonzero point with ζ(s) nonzero, the ordinary quotient "
                        + "rules give analyticity. Equality to T off 1 preserves its half-plane integral and "
                        + "its punctured expansions at the zeta zeros. Continuity at 1 forces the same "
                        + "limit for any other function agreeing with T everywhere else."))), DescribeRole.Theorem))));

    private static Formula Complex => F.Seq(F.Mathbb, F.Grp(F.Id("C")));
    private static Formula ComplexFunction => F.Seq(F.Open, Complex, F.Sp, F.To, F.Sp, Complex, F.Close);
    private static Formula At(string name, Formula s) =>
        new Formula.Apply(F.Id(name), [s]);
    private static Formula Equal(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Unequal(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula If(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Predicate(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula OffOne(string name)
    {
        var s = F.Id("s");
        return All("s", Complex, If(Unequal(s, F.D(1)), Equal(At(name, s), At("T", s))));
    }

    private static Formula Definition()
    {
        var derivative = new Formula.Apply(F.Seq(F.Id("A"), F.Apos), [F.D(1)]);
        return And(OffOne("F"), Equal(At("F", F.D(1)), Subtract(Add(F.D(1), F.GammaLower), derivative)));
    }

    private static Formula Claim()
    {
        var s = F.Id("s");
        var f = F.Id("F");
        var g = F.Id("G");
        var analytic = All("s", Complex, If(And(Unequal(s, F.D(0)),
            Unequal(new Formula.Apply(F.Zeta, [s]), F.D(0))), Predicate("AnalyticAt", Complex, f, s)));
        var unique = All("G", ComplexFunction, If(And(Predicate("ContinuousAt", g, F.D(1)), OffOne("G")),
            Equal(g, f)));
        return And(Definition(), And(analytic, unique));
    }
}
