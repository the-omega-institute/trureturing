using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Irrationality;

internal sealed class FibonacciSqrtFiveIrrationalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd Fibonacci-square-root-five layer constants are irrational.",
        H("Fibonacci Square-Root-Five Irrationality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("odd-layer-constant-irrationality"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/Irrationality/FibonacciSqrtFiveIrrationality."
                    + "odd_layer_constant_irrational"),
                H("Odd layer constants are irrational"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("m"), Eq, D(2), F.Id("k"), Plus, D(1), Sp, Implies, Sp,
                    Operatorname, Grp(F.Id("Irrational")), Open,
                    Frac, Grp(D(1)),
                    Grp(F.Id("F"), Underscore, F.Id("m"), Sp, Sqrt, Grp(D(5))),
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An odd index is positive, so its Fibonacci number is nonzero. The "
                        + "square root of five is irrational because five is prime. Multiplying "
                        + "by the nonzero Fibonacci number and then taking the reciprocal both "
                        + "preserve irrationality.")),
                    Paragraph(Text(
                        "This closes only the irrationality of the source atom's stated odd-layer "
                        + "expression 1/(F_m sqrt(5)). It does not identify an independently "
                        + "defined tower constant, prove the even-layer formula, or close any of "
                        + "the d = 48 preregistered claims."))),
                DescribeRole.Theorem))));
}
