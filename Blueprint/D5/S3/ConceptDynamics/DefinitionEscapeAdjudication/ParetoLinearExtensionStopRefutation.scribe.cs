using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeAdjudication;

internal sealed class ParetoLinearExtensionStopRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/"
            + "ParetoLinearExtensionStopRefutation."
            + "op5_pareto_stop_linear_extension_equivalences_refuted";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete sourced two-action model refutes both OP5 Pareto linear-extension stop equivalences.",
        H("OP5 Pareto Stop Equivalences Are Refuted"),
        Blocks(Describe.Lean(
            DescribeId.Create("op5-pareto-stop-linear-extension-equivalences-refuted"),
            DeclarationHandle.Create(Declaration),
            H("Dominance direction reverses the proposed stop characterizations"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The feasible carrier is Bool and the current action is true. True has "
                        + "strictly better values in all three benefit coordinates and strictly "
                        + "lower values in both cost coordinates, so it is both Pareto-maximal "
                        + "and Pareto-greatest under the frozen dominance convention.")),
                Paragraph(Text(
                    "Each LinearExtension value contains a complete linear order on the explicit "
                        + "finite Pareto quotient, a proof that it extends QuotientParetoWeak, "
                        + "and a full OrientationSpec. The latter preserves goal, source, and "
                        + "version and records the narrowed scope as the original scope paired "
                        + "with the feasible Finset.")),
                Paragraph(Text(
                    "A Szpilrajn extension witnesses that the extension family is nonempty. "
                        + "Every member places the dominating true class before the false class. "
                        + "OrientedStop rejects strict successors of current, hence no member "
                        + "stops at true and both displayed equivalences fail.")),
                Paragraph(Text(
                    "The displayed certificate includes every OP5 side condition: nonempty "
                        + "feasibility, the sealed feasible/current fields, admissibility and "
                        + "original-scope membership, maximality, greatestness, and extension "
                        + "nonemptiness. Repository, pinned-Mathlib, and third-party searches "
                        + "found no existing theorem with this sourced-stop statement."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula finiteCarrier = Call("feasible");
        Formula commitment = Call("commitment");
        Formula value = Call("value");
        Formula current = F.Id("true");
        Formula linearExtension = Call("LinearExtension");
        Formula action = F.Id("action");
        Formula extension = F.Id("L");
        Formula paretoOrientation = Call("paretoOrientation");

        Formula maximal = Call(
            "ParetoMaximalIn", value, finiteCarrier, current);
        Formula greatest = Call(
            "ParetoGreatestIn", value, finiteCarrier, current);
        Formula stop = Call(
            "OrientedStop",
            Call("admissibleTarget"),
            Call("InFiniteNarrowedScope", Call("inScope")),
            Call("orientation", extension),
            commitment);

        Formula modelCertificate = All(
            Call("Nonempty", finiteCarrier),
            Equal(Call("feasible", Call("decision", commitment)), finiteCarrier),
            Equal(Call("current", Call("decision", commitment)), Call("some", current)),
            ForAll(
                [Bound("action", Call("Bool"))],
                Implies(
                    Member(action, finiteCarrier),
                    And(
                        Member(
                            action,
                            Call(
                                "admissibleTarget",
                                Call("goal", paretoOrientation))),
                        Call(
                            "inScope",
                            Call("scope", paretoOrientation),
                            action)))),
            maximal,
            greatest,
            Call("Nonempty", linearExtension));

        Formula someStop = Exists(
            [Bound("L", linearExtension)],
            stop);
        Formula everyStop = ForAll(
            [Bound("L", linearExtension)],
            stop);

        return Disp(All(
            modelCertificate,
            Negate(Iff(maximal, someStop)),
            Negate(Iff(everyStop, greatest))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Member(Formula element, Formula set) =>
        new Formula.Relation(element, FormulaRelationOperator.MemberOf, set);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Negate(Formula formula) => new Formula.Not(formula);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
}
