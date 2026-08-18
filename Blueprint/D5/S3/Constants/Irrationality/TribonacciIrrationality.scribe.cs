using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Irrationality;

internal sealed class TribonacciIrrationalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var statement = Call("Irrational", Id("tribonacciConstant"));

        const string declarationPrefix =
            "D5/S3/Constants/Irrationality/TribonacciIrrationality.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The Tribonacci constant is irrational.",
            H("Tribonacci Irrationality"),
            Blocks(
                Paragraph(Text(
                    "The constant satisfies a monic cubic with integer coefficients, so a "
                        + "rational equal to it would have denominator dividing the cube of its "
                        + "numerator; being in lowest terms, that denominator is one and the "
                        + "constant would be an integer. It lies strictly between one and two, "
                        + "where there is no integer.")),
                Paragraph(Text(
                    "All three inputs were already in the tree: the defining cubic and the two "
                        + "bounds. What was absent was this conclusion. The quadratic base of "
                        + "the non-Pisot frontier has its irrationality; the cubic constant, "
                        + "which is older and more central, did not.")),
                Describe.Lean(
                    DescribeId.Create("the-tribonacci-constant-is-irrational"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tribonacciConstant_irrational"),
                    H("The Tribonacci constant is irrational"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Pinned Mathlib's irrationality lemma for n-th roots does not apply to a "
                            + "general cubic, so the argument is elementary rather than imported. "
                            + "The rational-root step uses the coprimality of numerator and "
                            + "denominator directly."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/Tribonacci/Values")),
            ]));
    }
}
