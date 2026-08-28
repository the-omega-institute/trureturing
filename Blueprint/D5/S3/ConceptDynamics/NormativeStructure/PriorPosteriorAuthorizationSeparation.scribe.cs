using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.NormativeStructure;

internal sealed class PriorPosteriorAuthorizationSeparationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/NormativeStructure/PriorPosteriorAuthorizationSeparation."
            + "posterior_approval_authorization_separation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A change can revise the standard by which the changed subject later authorizes it.",
        H("Prior and Posterior Authorization Separation"),
        Blocks(Describe.Lean(
            DescribeId.Create("posterior-approval-authorization-separation"),
            DeclarationHandle.Create(Declaration),
            H("Posterior approval does not establish prior authorization"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The authorization predicate evaluates the current approval standard on "
                        + "the action preference before and after the proposed change. It is "
                        + "constructed from those three source primitives.")),
                Paragraph(Text(
                    "The countermodel exposes its preference, approval standard, change, and "
                        + "original state as existential witnesses. The change flips both state "
                        + "components, so both revisions are part of the public statement.")),
                Paragraph(Text(
                    "The original approval bit rejects the preference transition. After the "
                        + "same process changes the subject, the new approval bit accepts the "
                        + "transition produced by applying that process again."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula proposition = F.Id("Prop");
        Formula state = Product(boolean, boolean);
        Formula preference = F.Id("A");
        Formula standard = F.Id("R");
        Formula change = F.Id("G");
        Formula original = F.Id("x");
        Formula changed = Apply(change, original);
        Formula prior = Authorizes(preference, standard, change, original);
        Formula posterior = Authorizes(preference, standard, change, changed);

        Formula clauses = And(
            NotEqual(Apply(preference, changed), Apply(preference, original)),
            And(
                NotEqual(Apply(standard, changed), Apply(standard, original)),
                And(
                    new Formula.Not(prior),
                    And(
                        posterior,
                        new Formula.Not(new Formula.Logic(
                            posterior,
                            FormulaLogicOperator.Implies,
                            prior))))));

        Formula witnesses = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("A"),
            Arrow(state, boolean),
            new Formula.Bind(
                FormulaQuantifier.Exists,
                FormulaIdentifier.Create("R"),
                Arrow(state, Arrow(boolean, Arrow(boolean, proposition))),
                new Formula.Bind(
                    FormulaQuantifier.Exists,
                    FormulaIdentifier.Create("G"),
                    Arrow(state, state),
                    new Formula.Bind(
                        FormulaQuantifier.Exists,
                        FormulaIdentifier.Create("x"),
                        state,
                        clauses))));

        return F.Disp(witnesses);
    }

    private static Formula Authorizes(
        Formula preference,
        Formula standard,
        Formula change,
        Formula state) =>
        Apply(F.Id("modificationAuthorized"), preference, standard, change, state);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Product(Formula left, Formula right) =>
        F.Seq(left, F.Sp, F.Times, F.Sp, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
