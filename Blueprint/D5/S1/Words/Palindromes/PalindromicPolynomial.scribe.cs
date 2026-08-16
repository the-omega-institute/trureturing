using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes;

internal sealed class PalindromicPolynomialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula ring = F.Id("R");
        Formula polynomial = F.Id("p");
        Formula index = F.Id("i");
        Formula degree = Call("natDegree", polynomial);
        Formula coefficient(Formula at) => Call("coeff", polynomial, at);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Palindromic coefficients make a polynomial equal to its coefficient reversal.",
            H("Palindromic Polynomials Are Self-Reciprocal"),
            Blocks(
                Paragraph(Text(
                    "This document closes only the structural implication from palindromic "
                        + "truncation to self-reciprocity in residual observation 6.156. It does "
                        + "not formalize the experimental zero locations, geometric accumulation, "
                        + "or root-on-circle preference stated nearby.")),
                Describe.Lean(
                    DescribeId.Create("palindromic-coefficients-give-self-reciprocity"),
                    DeclarationHandle.Create(
                        "D5/S1/Words/Palindromes/PalindromicPolynomial."
                            + "reverse_eq_self_of_palindromic_coefficients"),
                    H("Palindromic coefficients give self-reciprocity"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, ring, Comma, Sp,
                        Operatorname, Grp(F.Id("Semiring")), Open, ring, Close, Comma, Sp,
                        Forall, Sp, polynomial, InMacro,
                        Operatorname, Grp(F.Id("Polynomial")), Open, ring, Close, Comma, Sp,
                        Open, Forall, Sp, index, Comma, Sp, index, Sp, Le, Sp, degree,
                        Sp, Rightarrow, Sp, coefficient(index), Sp, Eq, Sp,
                        coefficient(Seq(degree, Sp, Minus, Sp, index)), Close,
                        Sp, Rightarrow, Sp, Call("reverse", polynomial), Sp, Eq, Sp, polynomial))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Polynomial extensionality reduces the claim to coefficients. Mathlib's "
                            + "coefficient formula for polynomial reversal changes an in-range "
                            + "index i to natDegree(p) minus i; the palindrome hypothesis closes "
                            + "that case, while reversal fixes indices above the degree."))),
                    DescribeRole.Theorem)),
            []));
    }
}
