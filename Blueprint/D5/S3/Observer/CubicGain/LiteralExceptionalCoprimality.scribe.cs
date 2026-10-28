using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class LiteralExceptionalCoprimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "FC and the displayed exceptional factor",
        H("The exceptional factor in the literal source identity"),
        Blocks(
            Paragraph(Text("F is the original criticalPolynomial, with precisely the sixty-eight integer coefficients FC. Write H over any commutative coefficient ring for X^90 (2X+1)^5 (5X+2)^14 (8X-1)^20 (X^2+8X+4)^2; exceptionalFactor is this expression. This is exactly the polynomial displayed on the right of the proposed h identity in VI, Lemma 4.2. No parameter or root is selected.")),
            Describe.Lean(DescribeId.Create("literal-displayed-exceptional-factor"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/LiteralExceptionalCoprimality.exceptionalFactor"),
                H("The displayed exceptional polynomial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any commutative coefficient ring R, exceptionalFactor in R[X] is the displayed expression H above, using the same exponents and integer coefficients."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("displayed-exceptional-factor-coprime"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/LiteralExceptionalCoprimality.displayed_exceptional_factor_coprime"),
                H("The displayed degree-133 factor is coprime to FC"),
                StatementSource.FromAuthor(Result()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integer polynomial H has natural degree 133, and its real coefficient image is coprime to F. Thus no zero of F is a zero of H. The square-free product G=X (2X+1) (5X+2) (8X-1) (X^2+8X+4) has degree six. Explicit integer polynomials U,V,W satisfy U F+V G=1+101 W. Reduction modulo 101 preserves degrees 67 and six and proves a nonzero fixed-degree resultant. Coefficient maps transfer this nonvanishing to the rationals; the resultant criterion and extension to the reals give coprimality with G. Splitting the five factors and restoring their original powers proves the assertion for H."))), DescribeRole.Theorem),
            Paragraph(Text("This result concerns the exact displayed H. The identity H=pp_positive(gcd(a0,c0)) for the original fixed minors has not been established here. Consequently it does not identify the actual gcd, determine the reduced a and c, or settle their degrees, their coprimalities, the degree-sixty quotients, or root and world exhaustion.")))));

    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Seq(args), Close);
    private static Formula Result() => Disp(Seq(
        Call("natDegree", Seq(F.Id("H"), Underscore, Grp(Mathbb, Grp(F.Id("Z"))))),
        Eq, Sp, D(1,3,3), Land, Sp,
        Call("IsCoprime", F.Id("F"), Comma, Sp,
            Seq(F.Id("H"), Underscore, Grp(Mathbb, Grp(F.Id("R")))))));
}
