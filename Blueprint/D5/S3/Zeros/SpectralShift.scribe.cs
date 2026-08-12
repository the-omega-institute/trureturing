using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class SpectralShiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Multiplicative address pullbacks act pointwise by the labeled-zeta character on the O-6 spectral foundation.",
        H("Multiplicative Address Shifts and Labeled Zeta"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-backward-shift-pulls-coefficients-along-address-addition"),
                DeclarationHandle.Create("D5/S3/Zeros/SpectralShift.backwardShift"),
                H("A backward shift pulls coefficients along address addition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(
                                    Text("For a supplied PrimeAxisTable address u and arbitrary coefficient family x, the definition evaluates x at the normalized table sum a plus u. It is a pointwise family pullback, not a bundled bounded Hilbert-space operator, an adjoint theorem, or the source's basis-level truncating divisibility operator. "),
                                    Ref("D5/L/hedenmalm1997hilbert"),
                                    Text(" supplies the Dirichlet coefficient-space context; the exact multi-axis pullback is repository-derived. It exposes the multiplicative character action that supports the spectral side of O-6 without postulating a Hilbert-Polya operator."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("labeled-zeta-coefficients-are-pointwise-shift-eigenfamilies"),
                DeclarationHandle.Create("D5/S3/Zeros/SpectralShift.labeled_zeta_backward_shift_eigen"),
                H("Labeled-zeta coefficients are pointwise shift eigenfamilies"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, Forall, Sp, F.Id("u"), Comma, F.Id("a"), InMacro, Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc, Operatorname, Grp(F.Id("backwardShift")), Open, F.Id("u"), Comma, Operatorname, Grp(F.Id("labeledZetaCoefficient")), Open, F.Id("s"), Close, Comma, F.Id("a"), Close, Eq, Operatorname, Grp(F.Id("labeledZetaCoefficient")), Open, F.Id("s"), Comma, F.Id("u"), Close, Operatorname, Grp(F.Id("labeledZetaCoefficient")), Open, F.Id("s"), Comma, F.Id("a"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(
                                    Text("At every supplied complex parameter and pair of prime addresses, pulling the labeled coefficient family backward by u multiplies the value at a by the labeled coefficient at u. The theorem is an exact consequence of normalized address multiplication and complex powers, with no summability hypothesis. It does not bundle simultaneous eigenvectors for operators or prove boundedness, adjointness, commutation, or completeness. "),
                                    Ref("D5/L/hedenmalm1997hilbert"),
                                    Text(" gives the established Dirichlet-series setting, while this address-level identity is the repository's algebraic translation. It strengthens the coefficient mechanics under the O-6 spectral foundation but supplies no zero-location conclusion."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-square-summable-labeled-vector-has-the-same-pointwise-eigen-action"),
                DeclarationHandle.Create("D5/S3/Zeros/SpectralShift.labeled_zeta_vector_backward_shift_eigen"),
                H("The square-summable labeled vector has the same pointwise eigen-action"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, Operatorname, Grp(F.Id("criticalAbscissa")), Lt, Re, Open, F.Id("s"), Close, Sp, Rightarrow, Sp, Forall, Sp, F.Id("u"), Comma, F.Id("a"), InMacro, Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc, Operatorname, Grp(F.Id("backwardShift")), Open, F.Id("u"), Comma, Operatorname, Grp(F.Id("labeledZetaVector")), Open, F.Id("s"), Close, Comma, F.Id("a"), Close, Eq, Operatorname, Grp(F.Id("labeledZetaCoefficient")), Open, F.Id("s"), Comma, F.Id("u"), Close, Operatorname, Grp(F.Id("labeledZetaVector")), Open, F.Id("s"), Comma, F.Id("a"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(
                                    Text("When the real part lies strictly to the right of the existing critical abscissa, the actual square-summable labeled-zeta vector satisfies the same equality at each supplied address. The half-plane premise is a typing witness for that vector; the result remains pointwise because backwardShift is not a bundled continuous operator. Compared with the CAS theorem, this omits the joint bounded-operator assertion, basis subtraction rule, Bloch-wave and Bost-Connes identifications, and numerical certificate. "),
                                    Ref("D5/L/hedenmalm1997hilbert"),
                                    Text(" is contextual rather than a verbatim source for this multi-axis claim. The theorem provides a concrete spectral action compatible with the O-6 Hilbert-space route, but neither constructs the positivity form nor connects eigenvalues to zeta zeros."))),
                DescribeRole.Theorem
            )),
[
                        DocumentEdge.Dependency.Create(
                            GidRef.Create("D5/S1/Digit/PrimeAxisAddition")),
                        DocumentEdge.Dependency.Create(
                            GidRef.Create("D5/S3/Weil/SpectralHilbert")),
                    ]));
}
