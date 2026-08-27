using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class GraphMechanismLawSeparationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/GraphMechanismLawSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed graph does not determine its mechanism, and an observational law does not "
            + "determine its graph.",
        H("Graph, Mechanism, and Law Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("same-graph-supports-distinct-mechanisms"),
                DeclarationHandle.Create(
                    Prefix + "same_graph_supports_distinct_mechanisms"),
                H("One graph supports distinct mechanisms"),
                StatementSource.FromAuthor(SameGraphFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Both witnesses use the existing X-causes-Y direction and the identity "
                            + "root. Their child mechanisms are identity and Boolean negation. "
                            + "At false the outputs are false and true, proving that the "
                            + "mechanisms differ while the encoded DAG remains fixed.")),
                    Paragraph(Text(
                        "This is a concrete two-node witness, not a general SCM framework. "
                            + "On an empty carrier functions are unique; on one edgeless node, "
                            + "different constant mechanisms still exist."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("opposite-graphs-same-observational-law"),
                DeclarationHandle.Create(
                    Prefix + "opposite_graphs_same_observational_law"),
                H("Opposite graphs share one observational law"),
                StatementSource.FromAuthor(SameLawFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The reused X-causes-Y and Y-causes-X constructors are unequal causal "
                            + "directions. With identity root and child mechanisms, both map "
                            + "each fair Boolean noise value u to the same observed pair (u,u), "
                            + "so their PMF pushforwards are equal.")),
                    Paragraph(Text(
                        "FPOD 268.1 instead concerns crosswise recombination of mechanism "
                            + "readouts. It provides neither distinct DAGs nor equality of PMFs "
                            + "and therefore cannot imply this graph-law witness. No prime "
                            + "parameter or primality fact is used."))),
                DescribeRole.Theorem))));

    private static Formula SameGraphFormula()
    {
        Formula identityModel = F.Id("MIdentity");
        Formula flippedModel = F.Id("MFlip");
        Formula sameDirection = Equal(
            ApplyFormula(F.Id("direction"), identityModel),
            ApplyFormula(F.Id("direction"), flippedModel));
        Formula differentChildren = NotEqual(
            ApplyFormula(F.Id("child"), identityModel),
            ApplyFormula(F.Id("child"), flippedModel));
        return F.Disp(new Formula.Logic(
            sameDirection,
            FormulaLogicOperator.And,
            differentChildren));
    }

    private static Formula SameLawFormula()
    {
        Formula forwardModel = F.Id("MXY");
        Formula reverseModel = F.Id("MYX");
        Formula differentDirections = NotEqual(
            ApplyFormula(F.Id("direction"), forwardModel),
            ApplyFormula(F.Id("direction"), reverseModel));
        Formula equalLaws = Equal(
            ApplyFormula(F.Id("observationalLaw"), forwardModel),
            ApplyFormula(F.Id("observationalLaw"), reverseModel));
        return F.Disp(new Formula.Logic(
            differentDirections,
            FormulaLogicOperator.And,
            equalLaws));
    }

    private static Formula ApplyFormula(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);
}
