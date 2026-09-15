using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class CoprimeSquarefreeDensityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The density of squarefree integers coprime to a fixed modulus.",
        H("Squarefree integers with a coprimality condition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("squarefree-coprime-count-error"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/CoprimeSquarefreeDensity.squarefree_coprime_count_error"),
                H("An explicit square-root error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every squarefree positive integer Q and nonnegative real X, let S(Q,X) "
                    + "count the positive squarefree integers at most X that are coprime to Q. "
                    + "The density rho(Q) is the reciprocal of the sum of the inverse squares of "
                    + "the positive integers, multiplied by p/(p+1) over the prime divisors p of Q. "
                    + "The real zeta series at two is written as the sum of ((n+1)^2) inverse "
                    + "over natural numbers n starting at zero. The absolute difference between "
                    + "S(Q,X) and rho(Q) times X is at most (2 to the number of distinct prime "
                    + "divisors of Q, plus 2) times the square root of X. The density is classical."))),
                DescribeRole.Theorem))));
}
