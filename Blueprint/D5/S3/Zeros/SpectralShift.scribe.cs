using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class SpectralShiftDocument : IScribeDocumentDefinition
{
    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Zeros/SpectralShift",
            "Multiplicative address pullbacks act pointwise by the labeled-zeta character on the O-6 spectral foundation."),
        H("Multiplicative Address Shifts and Labeled Zeta"),
        Blocks(
            DocumentBlock.Describe.Definition(
                DescribeId.Create("a-backward-shift-pulls-coefficients-along-address-addition"),
                H("A backward shift pulls coefficients along address addition"),
                LeanDefinition(
                    "D5/S3/Zeros/SpectralShift.backwardShift"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(
                    Text("For a supplied PrimeAxisTable address u and arbitrary coefficient family x, the definition evaluates x at the normalized table sum a plus u. It is a pointwise family pullback, not a bundled bounded Hilbert-space operator, an adjoint theorem, or the source's basis-level truncating divisibility operator. "),
                    Ref("D5/L/hedenmalm1997hilbert"),
                    Text(" supplies the Dirichlet coefficient-space context; the exact multi-axis pullback is repository-derived. It exposes the multiplicative character action that supports the spectral side of O-6 without postulating a Hilbert-Polya operator.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("labeled-zeta-coefficients-are-pointwise-shift-eigenfamilies"),
                H("Labeled-zeta coefficients are pointwise shift eigenfamilies"),
                LeanTheorem(
                    "D5/S3/Zeros/SpectralShift.labeled_zeta_backward_shift_eigen"),
                new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("C"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("u")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("PrimeAxisTable"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("backwardShift"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("u")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("labeledZetaCoefficient"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("labeledZetaCoefficient"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("u")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("labeledZetaCoefficient"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis)])),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(
                    Text("At every supplied complex parameter and pair of prime addresses, pulling the labeled coefficient family backward by u multiplies the value at a by the labeled coefficient at u. The theorem is an exact consequence of normalized address multiplication and complex powers, with no summability hypothesis. It does not bundle simultaneous eigenvectors for operators or prove boundedness, adjointness, commutation, or completeness. "),
                    Ref("D5/L/hedenmalm1997hilbert"),
                    Text(" gives the established Dirichlet-series setting, while this address-level identity is the repository's algebraic translation. It strengthens the coefficient mechanics under the O-6 spectral foundation but supplies no zero-location conclusion.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-square-summable-labeled-vector-has-the-same-pointwise-eigen-action"),
                H("The square-summable labeled vector has the same pointwise eigen-action"),
                LeanTheorem(
                    "D5/S3/Zeros/SpectralShift.labeled_zeta_vector_backward_shift_eigen"),
                new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("C"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("criticalAbscissa"))]), new Formula.LatexSymbol(FormulaLatexSymbol.LessThan), new Formula.LatexMacro(FormulaLatexMacro.Re), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Rightarrow), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("u")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("PrimeAxisTable"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("backwardShift"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("u")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("labeledZetaVector"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("labeledZetaCoefficient"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("u")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("labeledZetaVector"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis)])),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(
                    Text("When the real part lies strictly to the right of the existing critical abscissa, the actual square-summable labeled-zeta vector satisfies the same equality at each supplied address. The half-plane premise is a typing witness for that vector; the result remains pointwise because backwardShift is not a bundled continuous operator. Compared with the CAS theorem, this omits the joint bounded-operator assertion, basis subtraction rule, Bloch-wave and Bost-Connes identifications, and numerical certificate. "),
                    Ref("D5/L/hedenmalm1997hilbert"),
                    Text(" is contextual rather than a verbatim source for this multi-axis claim. The theorem provides a concrete spectral action compatible with the O-6 Hilbert-space route, but neither constructs the positivity form nor connects eigenvalues to zeta zeros.")))
            ))));
}
