using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HiddenFlow;

internal sealed class SupportExternalMechanismDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A mechanism value outside an accessed support can change without changing the observed channel.",
        H("Support-External Mechanism"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unseen-parent-config-can-change-without-observed-law"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/SupportExternalMechanism."
                        + "unseen_parent_config_can_change_without_observed_law"),
                H("An unseen parent configuration is not identified by the observed channel"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The support predicate is the set of parent configurations accessed by "
                            + "the behavior regime. The observation channel is the canonical "
                            + "restriction of a structural mechanism to that support.")),
                    Paragraph(Text(
                        "When a hidden configuration lies outside the support, two mechanisms "
                            + "can agree on every accessed parent and still take distinct values "
                            + "at the hidden parent. The Boolean corollary supplies a concrete "
                            + "nontrivial model.")),
                    Paragraph(Text(
                        "The theorem exposes both source clauses publicly: equality of observed "
                            + "channels and inequality of the hidden mechanism values."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TypeUniverse() => Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula SetOf(Formula carrier) => Call("Set", carrier);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula NotMember(Formula element, Formula set) =>
        new Formula.Not(Apply(set, element));

    private static Formula ObservationChannel(Formula support, Formula mechanism) =>
        Apply(Apply(F.Id("observationChannel"), support), mechanism);

    private static Formula TheoremFormula()
    {
        Formula parent = F.Id("Parent");
        Formula outcome = F.Id("Outcome");
        Formula support = F.Id("support");
        Formula hidden = F.Id("hidden");
        Formula mechanismType = Arrow(parent, outcome);
        Formula mechanism0 = F.Id("mechanism0");
        Formula mechanism1 = F.Id("mechanism1");
        Formula observedEquality = Equal(
            ObservationChannel(support, mechanism0),
            ObservationChannel(support, mechanism1));
        Formula hiddenInequality = NotEqual(
            Apply(mechanism0, hidden),
            Apply(mechanism1, hidden));
        Formula witnesses = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("mechanism0", mechanismType), Bound("mechanism1", mechanismType)],
            new Formula.Logic(observedEquality, FormulaLogicOperator.And, hiddenInequality));
        Formula supportPremise = new Formula.Logic(
            Call("Nontrivial", outcome),
            FormulaLogicOperator.And,
            NotMember(hidden, support));
        Formula quantified = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Parent", TypeUniverse()),
                Bound("Outcome", TypeUniverse()),
                Bound("support", SetOf(parent)),
                Bound("hidden", parent),
            ],
            new Formula.Logic(
                supportPremise,
                FormulaLogicOperator.Implies,
                witnesses));
        return Disp(quantified);
    }
}
