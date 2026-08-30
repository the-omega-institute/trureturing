using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeLaws;

internal sealed class ScientificGainGeneralizationReversalDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeLaws/"
            + "ScientificGainGeneralizationReversal."
            + "scientific_gain_generalization_sign_reversal";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite scientific-gain witness can have opposite conditional future loss signs.",
        H("Scientific Gain Does Not Identify Generalization"),
        Blocks(Describe.Lean(
            DescribeId.Create("scientific-gain-generalization-sign-reversal"),
            DeclarationHandle.Create(Declaration),
            H("Equal observed marginals admit opposite future loss signs"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The two explicitly normalized Unit-by-Bool joint laws have values in the "
                        + "unit interval and the same complete observed marginal. Their common "
                        + "history has positive mass, and its designated last record is the one "
                        + "used by ScientificGain.")),
                Paragraph(Text(
                    "Both actions' losses are explicitly absolutely summable under both finite "
                        + "laws. The loss and its difference use the same evaluator, frozen "
                        + "commitment comparator, and total next-evidence map as ScientificGain.")),
                Paragraph(Text(
                    "Conditioning the first law puts all future mass on the record where the "
                        + "committed action wins, giving loss difference minus one. Conditioning "
                        + "the second puts all mass on the record where the ranking reverses, "
                        + "giving plus one."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula unit = Call("Unit");
        Formula boolean = Call("Bool");
        Formula real = Call("Real");
        Formula observedNext = F.Seq(unit, F.Sp, F.Times, F.Sp, boolean);
        Formula jointLaw = Arrow(observedNext, real);
        Formula nextEvidenceType = Arrow(boolean, boolean);
        Formula lastEvidenceType = Arrow(unit, boolean);
        Formula evaluatorType = Arrow(unit, Arrow(boolean, Arrow(boolean, real)));
        Formula commitment = Call("WitnessCommitment");

        Formula p = F.Id("P"), q = F.Id("Q");
        Formula nextEvidence = F.Id("nextEvidence");
        Formula lastEvidence = F.Id("lastEvidence");
        Formula evaluate = F.Id("evaluate");
        Formula k = F.Id("K"), history = F.Id("h");
        Formula hStar = F.Id("hStar"), zStar = F.Id("zStar");
        Formula a = F.Id("a"), b = F.Id("b"), action = F.Id("action");
        Formula zero = D(0);
        Formula comparator = Call("comparator", k);

        Formula allObservedMarginals = ForAll(
            [Bound("h", unit)],
            Equal(Call("marginal", p, history), Call("marginal", q, history)));
        Formula commonHistoryMarginal = Equal(
            Call("marginal", p, hStar),
            Call("marginal", q, hStar));
        Formula positiveHistory = Less(zero, Call("marginal", p, hStar));
        Formula lastRecord = Equal(Apply(lastEvidence, hStar), zStar);
        Formula scientificGain = Call("ScientificGain", evaluate, k, zStar, a, b);
        Formula integrability = ForAll(
            [Bound("action", boolean)],
            And(
                Call(
                    "AbsolutelyIntegrableLoss",
                    p, evaluate, comparator, nextEvidence, action),
                Call(
                    "AbsolutelyIntegrableLoss",
                    q, evaluate, comparator, nextEvidence, action)));
        Formula pDifference = Call(
            "conditionalExpectedLossDifference",
            p, hStar, evaluate, comparator, nextEvidence, a, b);
        Formula qDifference = Call(
            "conditionalExpectedLossDifference",
            q, hStar, evaluate, comparator, nextEvidence, a, b);

        Formula clauses = All(
            Call("IsFiniteJointLaw", p),
            Call("IsFiniteJointLaw", q),
            allObservedMarginals,
            commonHistoryMarginal,
            positiveHistory,
            lastRecord,
            scientificGain,
            integrability,
            Less(pDifference, zero),
            Less(zero, qDifference));

        return Disp(Exists(
            [
                Bound("P", jointLaw),
                Bound("Q", jointLaw),
                Bound("nextEvidence", nextEvidenceType),
                Bound("lastEvidence", lastEvidenceType),
                Bound("evaluate", evaluatorType),
                Bound("K", commitment),
                Bound("hStar", unit),
                Bound("zStar", boolean),
                Bound("a", boolean),
                Bound("b", boolean),
            ],
            clauses));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

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
