using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.MetricGeometry;

internal sealed class CantorTransportExponentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Tower/MetricGeometry/CantorTransportExponent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Cantor exponent converts every positive triadic scale to its binary scale and defeats every Lipschitz constant.",
        H("Cantor Transport Exponent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cantor-exponent"),
                DeclarationHandle.Create(Prefix + "cantorExponent"),
                H("Cantor exponent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The transport exponent is log two divided by log three. Both logarithms "
                        + "are evaluated at positive arguments greater than one, so the quotient "
                        + "does not enter Lean's totalized nonpositive logarithm branch."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("triadic-scale"),
                DeclarationHandle.Create(Prefix + "triadicScale"),
                H("Positive-depth triadic scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At depth Q this source scale is three to the negative Q-plus-one power."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binary-scale"),
                DeclarationHandle.Create(Prefix + "binaryScale"),
                H("Positive-depth binary scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At depth Q this transported scale is two to the negative Q-plus-one power."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cantor-transport-exponent"),
                DeclarationHandle.Create(Prefix + "cantor_transport_exponent"),
                H("Exact Hölder conversion and Lipschitz obstruction"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The exponent lies strictly between zero and one. At every positive "
                            + "depth, raising the triadic scale to that exponent gives exactly "
                            + "the corresponding binary scale.")),
                    Paragraph(Text(
                        "The exact scale identity uses Mathlib's logarithm of a real power and "
                            + "real-power multiplication laws. Positivity of the bases is proved "
                            + "before applying those laws.")),
                    Paragraph(Text(
                        "For every proposed positive Lipschitz constant K, geometric divergence "
                            + "of three-halves supplies a depth where the binary scale exceeds K "
                            + "times the triadic scale. Thus the exponent change is not merely a "
                            + "symbolic logarithm identity.")),
                    Paragraph(Text(
                        "This theorem records the metric-scale part of the source claim. It does "
                            + "not assert the separate measure-pushforward statement for the "
                            + "Cantor function."))),
                DescribeRole.Theorem)),
        []));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula TheoremFormula()
    {
        var alpha = Id("alpha");
        var q = Id("Q");
        var constant = Id("K");
        var naturals = Id("N");
        var reals = Id("R");
        var triadic = Call("d3", q);
        var binary = Call("d2", q);

        var exponentBounds = And(
            new Formula.Relation(Num(0), FormulaRelationOperator.LessThan, alpha),
            new Formula.Relation(alpha, FormulaRelationOperator.LessThan, Num(1)));
        var exactConversion = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("Q"),
            naturals,
            Equal(Call("rpow", triadic, alpha), binary));
        var lipschitzFailure = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("K"),
            reals,
            new Formula.Logic(
                new Formula.Relation(Num(0), FormulaRelationOperator.LessThan, constant),
                FormulaLogicOperator.Implies,
                new Formula.Bind(
                    FormulaQuantifier.Exists,
                    FormulaIdentifier.Create("Q"),
                    naturals,
                    new Formula.Relation(
                        Multiply(constant, triadic),
                        FormulaRelationOperator.LessThan,
                        binary))));

        return And(exponentBounds, And(exactConversion, lipschitzFailure));
    }
}
