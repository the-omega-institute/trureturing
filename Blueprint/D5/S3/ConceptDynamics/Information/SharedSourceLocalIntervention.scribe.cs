using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Information;

internal sealed class SharedSourceLocalInterventionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixing one coordinate leaves a distinct shared-source coordinate fair and unfixed.",
        H("Shared-Source Local Intervention"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-intervention-exposes-shared-source"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Information/SharedSourceLocalIntervention."
                        + "local_intervention_exposes_shared_source"),
                H("A local intervention exposes the retained shared source"),
                StatementSource.FromAuthor(InterventionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p and q be distinct decidable addresses. The local intervention "
                            + "replaces the value at p by an imposed Boolean value, while the "
                            + "value queried at q remains the Boolean source.")),
                    Paragraph(Text(
                        "With mass one half on each source state, the q-coordinate therefore "
                            + "retains mass one half at each Boolean value. It also differs from "
                            + "the imposed p-coordinate with probability one half."))),
                DescribeRole.Theorem))));

    private static Formula InterventionFormula()
    {
        Formula address = F.Id("Address");
        Formula boolType = F.Id("Bool");
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula imposed = F.Id("imposed");
        Formula source = F.Id("source");
        Formula observed = F.Id("observed");
        Formula half = new Formula.Fraction(new Formula.Number(1), new Formula.Number(2));
        Formula distinct = NotEqual(p, q);
        Formula response = Call("ite", Equal(q, p), imposed, source);
        Formula fairLaw = LambdaFormula(F.Id("fairSource"), half);
        Formula coordinateReadout = LambdaFormula(source, response);
        Formula mismatchReadout = LambdaFormula(
            source,
            Call("decide", NotEqual(response, imposed)));

        Formula conclusion = And(
            Equal(response, source),
            And(
                Equal(
                    Call("conceptLaw", fairLaw, coordinateReadout, observed),
                    half),
                Equal(
                    Call("conceptLaw", fairLaw, mismatchReadout, F.Id("true")),
                    half)));
        Formula quantifiedConclusion = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("imposed", boolType),
                Bound("source", boolType),
                Bound("observed", boolType),
            ],
            conclusion);

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("Address", F.Id("Type")), Bound("p", address), Bound("q", address)],
            Implies(
                And(Call("DecidableEq", address), distinct),
                quantifiedConclusion)));
    }

    private static Formula LambdaFormula(Formula variable, Formula body) =>
        Seq(Lambda, Sp, variable, Comma, Sp, body);

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
