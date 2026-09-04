using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.TransportValidity;

internal sealed class PredicateRestrictedValidityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/TransportValidity/PredicateRestrictedValidity."
            + "predicate_valid_on_restricted_admission";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Restricting admission by a predicate makes that predicate valid.",
        H("Predicate-Restricted Validity"),
        Blocks(Describe.Lean(
            DescribeId.Create("predicate-valid-on-restricted-admission"),
            DeclarationHandle.Create(Declaration),
            H("The restricting predicate is valid on the updated domain"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For arbitrary predicates A and P on X, the updated admission predicate "
                    + "at x is exactly A(x) and P(x). Its right conjunct therefore gives "
                    + "P(x) for every state in the updated domain."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula sort = F.Id("Sort");
        Formula proposition = F.Id("Prop");
        Formula carrier = F.Id("X");
        Formula admission = F.Id("A");
        Formula predicate = F.Id("P");
        Formula x = F.Id("x");
        Formula predicateType = Arrow(carrier, proposition);

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", sort),
                Bound("A", predicateType),
                Bound("P", predicateType),
                Bound("x", carrier),
            ],
            Implies(
                And(Apply(admission, x), Apply(predicate, x)),
                Apply(predicate, x))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
}
