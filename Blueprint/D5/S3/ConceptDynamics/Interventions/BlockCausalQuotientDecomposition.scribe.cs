using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interventions;

internal sealed class BlockCausalQuotientDecompositionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Block-product intervention channels decompose causal equivalence and its quotient.",
        H("Block Causal Quotient Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("causal-equivalence-block-decomposition"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Interventions/"
                        + "BlockCausalQuotientDecomposition."
                        + "causal_equivalence_block_decomposition"),
                H("Causal equivalence and the causal quotient decompose by blocks"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the block index be finite. Each block has a nonempty allowed "
                            + "intervention type and a local response channel. A joint "
                            + "intervention is the unrestricted product of those local "
                            + "interventions, and its response is assembled coordinatewise.")),
                    Paragraph(Text(
                        "Two block models agree under every joint intervention exactly when "
                            + "their local channels agree under every intervention in every "
                            + "block. The reverse direction inserts a chosen local action into "
                            + "a baseline joint intervention.")),
                    Paragraph(Text(
                        "The global and local causal quotients use the existing empirical "
                            + "setoid. The named canonical equivalence is Mathlib's indexed "
                            + "quotient-product equivalence after transporting along the first "
                            + "clause, and it sends each global class to its family of local "
                            + "classes."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula modelType = Call("BlockModel", indexType);
        Formula jointInterventionType = Call("JointIntervention", indexType);
        Formula firstModel = F.Id("M");
        Formula secondModel = F.Id("N");
        Formula jointIntervention = F.Id("a");
        Formula block = F.Id("i");
        Formula localIntervention = F.Id("u");

        Formula globalAgreement = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("a", jointInterventionType)],
            Equal(
                Call("blockInterventionalOutcome", jointIntervention, firstModel),
                Call("blockInterventionalOutcome", jointIntervention, secondModel)));

        Formula localAgreement = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [Bound("u", Call("Action", block))],
                Equal(
                    Call("apply", firstModel, block, localIntervention),
                    Call("apply", secondModel, block, localIntervention))));

        Formula equivalenceClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("M", modelType), Bound("N", modelType)],
            new Formula.Logic(
                globalAgreement,
                FormulaLogicOperator.Iff,
                localAgreement));

        Formula quotientClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("M", modelType)],
            Equal(
                Call(
                    "causalQuotientEquiv",
                    Call("globalClass", firstModel)),
                Call("localClasses", firstModel)));

        return F.Disp(new Formula.Logic(
            equivalenceClause,
            FormulaLogicOperator.And,
            quotientClause));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
