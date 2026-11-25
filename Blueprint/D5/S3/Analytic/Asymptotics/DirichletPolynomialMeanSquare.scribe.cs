using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class DirichletPolynomialMeanSquareDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mean squares of finite Dirichlet polynomials",
        H("Mean squares of finite Dirichlet polynomials"),
        Blocks(Describe.Lean(
            DescribeId.Create("vertical-mean-square-le"),
            DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/DirichletPolynomialMeanSquare.vertical_mean_square_le"),
            H("A vertical mean square with initial cancellation"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("When the coefficients vanish through X and satisfy a uniform subpower envelope, the "
                + "diagonal sum starts above X. The off-diagonal sum costs a logarithm times the weighted "
                + "squared coefficients. Splitting close and separated pairs controls their reciprocal "
                + "logarithmic frequency gaps."))),
            DescribeRole.Theorem))));
}
