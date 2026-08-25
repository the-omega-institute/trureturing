using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeAdjudication;

internal sealed class TargetChangeSettlementConservationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/"
            + "TargetChangeSettlementConservation."
            + "append_only_old_settlement_unchanged";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Appending only later target versions preserves every old pure settlement.",
        H("Target-Change Settlement Conservation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("append-only-old-settlement-unchanged"),
                DeclarationHandle.Create(Declaration),
                H("Old-round settlement is unchanged by an append-only extension"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A target change records the old and new target versions together "
                            + "with reason, author, time, and affected rounds, so the "
                            + "version edge is explicit rather than an in-place mutation.")),
                    Paragraph(Text(
                        "RoundRecord stores the target version, immutable commitment, and "
                            + "evidence. AppendOnly means that a later ledger is the old "
                            + "ledger followed by a tail, and settleAt is a pure lookup and "
                            + "evaluation of one indexed record.")),
                    Paragraph(Text(
                        "For an old index that exists in the old ledger, List.get?_append "
                            + "returns the same record after any tail. Mapping the pure "
                            + "evaluator over that equal lookup proves the displayed "
                            + "settlement equality; mutable external state is not part of "
                            + "this evaluator interface."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula target = F.Id("Target");
        Formula commitment = F.Id("Commitment");
        Formula evidence = F.Id("Evidence");
        Formula verdict = F.Id("Verdict");
        Formula evaluate = F.Id("evaluate");
        Formula old = F.Id("old");
        Formula next = F.Id("new");
        Formula round = F.Id("round");
        Formula record = Call("RoundRecord", target, commitment, evidence);
        Formula ledger = Call("List", record);
        Formula evaluateType = Arrow(commitment, Arrow(evidence, verdict));
        Formula appendPremise = Call("AppendOnly", old, next);
        Formula boundPremise = new Formula.Relation(
            round,
            FormulaRelationOperator.LessThan,
            Call("length", old));
        Formula conclusion = new Formula.Relation(
            Call("settleAt", evaluate, next, round),
            FormulaRelationOperator.Equal,
            Call("settleAt", evaluate, old, round));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("Target"), F.Id("Type")),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("Commitment"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("Evidence"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("Verdict"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("evaluate"), evaluateType),
                new Formula.BoundVariable(FormulaIdentifier.Create("old"), ledger),
                new Formula.BoundVariable(FormulaIdentifier.Create("new"), ledger),
                new Formula.BoundVariable(FormulaIdentifier.Create("round"), F.Id("Nat")),
            ],
            new Formula.Logic(
                new Formula.Logic(
                    appendPremise,
                    FormulaLogicOperator.And,
                    boundPremise),
                FormulaLogicOperator.Implies,
                conclusion)));
    }
}
