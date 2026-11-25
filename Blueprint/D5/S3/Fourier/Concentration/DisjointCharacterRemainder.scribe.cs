using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class DisjointCharacterRemainderDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/DisjointCharacterRemainder";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjugate phases resolve each overlap contribution into a signed real square.",
        H("Signed overlap contributions and degree-sensitive remainder"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signed-overlap-expansion"),
                DeclarationHandle.Create(Owner + ".signed_overlap_expansion"),
                H("Signed mixed coefficients"),
                StatementSource.FromAuthor(Expansion()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let s be any finite index set and a any complex phase family. "
                        + "Set c to the sum of a over s. Let Q be the product over s of the factors "
                        + "exp(a(j)x) + exp(conj(a(j))y) - 1, and let C(T) be the degree-d coefficient "
                        + "of exp(cx) times the product over T of exp(-a(j)x) - 1. The bound B(T) "
                        + "is zero for |T| > d. For |T| ≤ d it is the product of |a(j)| on T times "
                        + "(|c| plus the sum of |a(j)| on T)^(d-|T|)/(d-|T|)!.")),
                    Paragraph(Text("Use the disjoint coefficient factorization. In the second variable each "
                        + "local correction is the negative of the conjugate correction in the first "
                        + "variable. Conjugation commutes with extraction of coefficients and the finite "
                        + "product. A subset therefore contributes a real square with sign determined "
                        + "by its cardinality.")),
                    Paragraph(Text("The complex exponential tail at an index is majorized coefficient by "
                        + "coefficient by |a(j)| x exp(|a(j)|x), since 1/n! ≤ 1/(n-1)! for n≥1. "
                        + "The Cauchy product preserves coefficientwise domination of norms by nonnegative "
                        + "coefficients. Multiplying the majorants extracts |T| powers of x and adds the "
                        + "real exponents, proving B(T) including the vanishing at insufficient degree."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-overlap-remainder"),
                DeclarationHandle.Create(Owner + ".signed_overlap_remainder"),
                H("Parity bounds for a truncated sum"),
                StatementSource.FromAuthor(Remainder()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For arbitrary natural numbers d and K take the real part of the "
                        + "mixed coefficient and subtract the alternating sum over subsets T with "
                        + "|T|≤min(d,K). Denote the resulting remainder by R. The large subsets "
                        + "satisfy K<|T|≤d. E and O designate their even and odd cardinality classes.")),
                    Paragraph(Text("Split the expansion into the retained part and these two classes. "
                        + "The even class contributes positive squares and the odd class contributes negative "
                        + "squares. Their exact difference and the coefficientwise bound give the stated "
                        + "one-sided errors. For K≥d the remainder is zero. For a cyclic character with "
                        + "a(j)=w(j) times the character, the same inequalities can be summed against the "
                        + "nonnegative Fejér weights. Bounds for the remaining weighted character sums of "
                        + "zeta ordinates at the growing degree and time scale require additional arithmetic."))),
                DescribeRole.Theorem))));

    private static Formula Expansion()
    {
        var t = F.Id("T");
        var d = F.Id("d");
        var c = Call("C", t);
        var q = F.Id("Q");
        var sign = new Formula.Power(Seq(Open, Minus, D(1), Close), Seq(Bar, t, Bar));
        var sum = new Formula.Subscript(Sum, Seq(t, Subseteq, F.Id("s"), Comma, Bar, t, Bar, Le, d));
        return Disp(new Formula.Aligned([
            Seq(Amp, OpenBracket, new Formula.Power(F.Id("x"), d), new Formula.Power(F.Id("y"), d),
                CloseBracket, q, Eq, sum, sign, new Formula.Power(Seq(Bar, c, Bar), D(2))),
            Seq(Amp, Forall, Sp, t, Subseteq, F.Id("s"), Comma, Sp, Bar, c, Bar, Le, Call("B", t))]));
    }

    private static Formula Remainder()
    {
        var t = F.Id("T");
        var r = F.Id("R");
        var even = new Formula.Subscript(Sum, Seq(t, InMacro, F.Id("E")));
        var odd = new Formula.Subscript(Sum, Seq(t, InMacro, F.Id("O")));
        var b = new Formula.Power(Call("B", t), D(2));
        var c = new Formula.Power(Seq(Bar, Call("C", t), Bar), D(2));
        return Disp(new Formula.Aligned([
            Seq(Amp, r, Eq, even, c, Minus, odd, c),
            Seq(Amp, Minus, odd, b, Le, r, Le, even, b)]));
    }
}
