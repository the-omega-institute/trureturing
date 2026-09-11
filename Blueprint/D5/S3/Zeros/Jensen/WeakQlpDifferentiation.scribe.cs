using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class WeakQlpDifferentiationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/Jensen/WeakQlpDifferentiation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational cubic refutes differentiation closure of the weak q-Laguerre-Polya class.",
        H("Weak q-Laguerre-Polya Differentiation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalized-q-borel"),
                DeclarationHandle.Create(Prefix + "qBorel"),
                H("Normalized q-Borel transform"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "B(q,f) denotes the real polynomial qBorel q f. If c(k) is the ordinary "
                    + "coefficient of X^k in f, its image coefficient is c(k) times k! times "
                    + "q raised to k(k-1)/2, times (1-q)^k, divided by the product of "
                    + "1-q^(j+1) for j from zero to k-1. The empty product is one. The "
                    + "factor k! converts ordinary coefficients to the exponential "
                    + "coefficients used by the normalized transform. Division is total; "
                    + "the claim only uses q strictly between zero and one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("half-counterexample"),
                DeclarationHandle.Create(Prefix + "halfCounterexample"),
                H("The rational cubic"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("f"), Eq, D(1), Plus,
                    D(3), Sp, F.Id("X"), Plus, Fraction(D(9), D(2)), Sp,
                    Pow(F.Id("X"), D(2)), Plus, Fraction(D(7), D(2)), Sp,
                    Pow(F.Id("X"), D(3))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here f is halfCounterexample, a polynomial over the real numbers "
                    + "with the displayed ordinary coefficients. At q equal to one half, "
                    + "its normalized transform is (X+1)^3."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("question62-claim"),
                DeclarationHandle.Create(Prefix + "Question62Claim"),
                H("The polynomial closure assertion"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("A"), Iff, ClaimFormula()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A denotes Question62Claim. Splits means splitting into linear factors "
                    + "over the real numbers, including zero and constants. The prime "
                    + "denotes polynomial differentiation. A real polynomial belongs to "
                    + "the classical Laguerre-Polya class exactly when it splits over the "
                    + "reals. Thus differentiation closure of the entire-function weak "
                    + "class would imply A. This analytic interpretation is not formalized "
                    + "as an additional theorem here."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("question62-refuted"),
                DeclarationHandle.Create(Prefix + "question62_refuted"),
                H("Differentiation closure is refuted"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, F.Id("A")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Substitute q equal to one half and the displayed cubic. Its transform "
                    + "is (X+1)^3, which splits. The transform of its derivative is "
                    + "7X^2+9X+3. A real root x would force the discriminant, minus three, "
                    + "to equal (14x+9)^2. Square nonnegativity contradicts this equality, "
                    + "so the nonconstant quadratic cannot split."))),
                DescribeRole.Theorem))));

    private static Formula ClaimFormula()
    {
        Formula q = F.Id("q");
        Formula f = F.Id("f");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        return Seq(Forall, Sp, q, InMacro, real, Comma, Sp,
            D(0), Lt, q, Sp, Rightarrow, Sp, q, Lt, D(1), Sp, Rightarrow, Sp,
            Forall, Sp, f, InMacro, real, OpenBracket, F.Id("X"), CloseBracket, Comma, Sp,
            Call("Splits", Call("B", q, f)), Sp, Rightarrow, Sp,
            Call("Splits", Call("B", q, Seq(f, Apos))));
    }

    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
