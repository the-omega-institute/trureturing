using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PauliLinearCertificateDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, Formula x, Formula y) =>
        Seq(Operatorname, Grp(V(name)), Open, x, Comma, y, Close);
    private static Formula Root(Formula x) => Seq(Sqrt, Grp(x));
    private static Formula Fraction(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original positive denominator linear certificate is strictly smaller than the quadratic root and its cap.",
        H("Strict comparison with the original root and cap"),
        Blocks(
            Paragraph(Text("The constant is one plus twice the square root of two. "
                + "The linear expression is twice the constant times d times epsilon, divided by the square root of two minus twice the constant times epsilon. "
                + "The old expression is the minimum of d and half of the constant times epsilon plus the square root of its square plus four times the constant times d times epsilon.")),
            Describe.Lean(DescribeId.Create("strict-comparison"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PauliLinearCertificate.strict_comparison"),
                H("The cap is included in the strict inequality"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, V("e"), Comma, V("d"), Sp,
                    InMacro, Sp, Mathbb, Grp(V("R")), Comma, Sp,
                    D(0), Lt, V("e"), Lt, Fraction(D(1), Seq(D(1,6), V("C"))), Comma, Sp,
                    D(1), Le, V("d"), Le, Root(D(2)), Sp, Rightarrow, Sp,
                    D(0), Lt, Root(D(2)), Minus, D(2), V("C"), V("e"), Sp, Land, Sp,
                    Call("linear", V("e"), V("d")), Lt, Call("old", V("e"), V("d"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For x equal to the constant times epsilon, the assumptions give zero less than x less than one sixteenth. "
                    + "The positive denominator bounds the linear expression by four x. This is strictly below the square root of x, "
                    + "which is at most the old quadratic root, and the linear expression is also strictly below one and hence below d. "
                    + "Both parts of the original minimum are therefore strictly larger. No defect estimate or general residual theorem is assumed here."))),
                DescribeRole.Theorem))));
}
