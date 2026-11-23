using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class SpectrumLogarithmicMissingWindowModelDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Oscillation/SpectrumLogarithmicMissingWindowModel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourth-root bins realize the logarithmic square-tail bound.",
        H("An Infinite Spectrum for the Logarithmic Waiting Gain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-infinite-logarithmic-model"),
                DeclarationHandle.Create(Owner + ".exists_infinite_logarithmic_model"),
                H("An infinite model for the logarithmic waiting gain"),
                StatementSource.FromAuthor(Model()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use the same rationally independent fourth-root bins and strictly "
                    + "positive weights. Their square tail is at most B/X² for a "
                    + "fixed B > 0 whenever X ≥ 1. Once log X ≥ 1, this is at most "
                    + "B log X/X uniformly in T ≥ X. "),
                    Ref("D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindowModel"
                        + ".exists_infinite_critical_model"),
                    Ref("D5/S3/Analytic/Oscillation/SpectrumLogarithmicMissingWindow"
                        + ".eventual_logarithmic_missing_window"))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);

    private static Formula Model()
    {
        var s = F.Id("S");
        var w = F.Id("w");
        var index = Call("index", s);
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var rats = Seq(Mathbb, Grp(F.Id("Q")));
        var positive = Bind(FormulaQuantifier.ForAll, "j", index,
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, Call("w", F.Id("j"))));
        return Disp(Bind(FormulaQuantifier.Exists, "S", F.Id("Spectrum"),
            Bind(FormulaQuantifier.Exists, "w", Seq(index, Sp, To, Sp, reals),
                And(Call("Infinite", index), And(positive,
                    And(Call("LinearIndependent", rats, Call("gamma", s)),
                        And(Call("HasLogSquaredMass", s, w), Call("HasLogarithmicSquareTail", s, w))))))));
    }
}
