using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class LiteralCriticalCoprimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coprimality of the literal critical polynomial and its derivative",
        H("The full FC coefficient list"),
        Blocks(
            Paragraph(Text("F is exactly criticalPolynomial from ExactW3Center: the sixty-eight descending integer coefficients FC of VI, Lemma 4.2 and Section 10, interpreted as a real polynomial. No root, interval or specialized source parameter is selected.")),
            Paragraph(Text("An integer polynomial with those same coefficients reduces modulo 101 to a degree-67 polynomial whose derivative has degree 66. Explicit integer polynomials satisfy U F + V F'=1+101 W. Reduction gives a full Bezout identity over ZMod 101, which proves that the modular resultant is nonzero. Compatibility of the fixed-degree resultant with coefficient homomorphisms then proves that the integer and rational resultants are nonzero. The resultant criterion gives coprimality over the rationals, and coefficient extension gives the stated real-polynomial conclusion.")),
            Describe.Lean(DescribeId.Create("literal-critical-polynomial-coprime-derivative"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/LiteralCriticalCoprimality.critical_polynomial_is_coprime_derivative"),
                H("The original FC has no repeated algebraic factor"),
                StatementSource.FromAuthor(Result()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal criticalPolynomial and its formal derivative are coprime. Equivalently, their gcd is a nonzero constant. The proof first establishes this statement over Q and then over R; it requires no assumption about any particular root."))), DescribeRole.Theorem),
            Paragraph(Text("This proves the F,F' coprimality clause alone. The original fixed determinant identities, both primitive gcd factorizations, the identification of h and the reduced a,c, their other coprimalities, and the complete root, lift and world exhaustion remain separate obligations.")))));

    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Seq(args), Close);
    private static Formula Result() => Disp(Call("IsCoprime", Call("criticalPolynomial"), Comma, Sp, Call("derivative", Call("criticalPolynomial"))));
}
