using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Crossing;

internal sealed class ThirdOrderReciprocityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjugation by the reciprocity matrix K reverses a matrix to its adjugate iff it is trace-orthogonal to K.",
        H("The Third-Order Reciprocity Linear Constitution"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("third-order-reciprocity-k-reversal-iff-trace-orthogonal"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/Crossing/ThirdOrderReciprocity.k_reversal_iff"),
                H("K conjugates gamma to its adjugate iff gamma is trace-orthogonal to K"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("K"), Sp, Eq, Sp,
                    Begin, Grp(F.Id("pmatrix")),
                    D(1), Amp, Minus, D(2), RowBreak, D(2), Amp, Minus, D(1),
                    End, Grp(F.Id("pmatrix")), Comma, Sp,
                    F.Id("K"), Caret, D(2), Sp, Eq, Sp, Minus, D(3), Sp, F.Id("I"), RowBreak,
                    F.Id("K"), Sp, GammaLower, Sp, Operatorname, Grp(F.Id("adj")), Sp, F.Id("K"), Sp,
                    Eq, Sp, D(3), Sp, Operatorname, Grp(F.Id("adj")), Sp, GammaLower, Sp,
                    Iff, Sp,
                    Operatorname, Grp(F.Id("tr")), Open, GammaLower, Sp, F.Id("K"), Close, Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The third-order reciprocity matrix K = [[1,-2],[2,-1]] is an integer 2x2 matrix with "
                        + "det K = 3 and K^2 = -3*I, so it behaves as a square root of -3. For every integer "
                        + "2x2 matrix gamma, conjugation by K reverses gamma to (det K) times its adjugate — "
                        + "that is, K*gamma*adj(K) = 3*adj(gamma) — exactly when gamma is trace-orthogonal to K, "
                        + "tr(gamma*K) = 0. The adjugate form is inverse-free, so the identity holds for all "
                        + "gamma including singular ones (for invertible gamma, adj(gamma) = det(gamma)*gamma^{-1})."
                        )),
                    Paragraph(Text(
                        "The trace tr(gamma*K) reduces to the linear form g00 + 2*g01 - 2*g10 - g11. Because K "
                        + "is traceless, the 2x2 Cayley-Hamilton polarization gives K*gamma + gamma*K = "
                        + "(tr gamma)*K + tr(gamma*K)*I, and every entry of K*gamma*adj(K) - 3*adj(gamma) collapses "
                        + "to that same linear form; hence the matrix equation holds iff the trace vanishes. The "
                        + "forward direction reads off entry (0,0); the backward direction checks all four entries.")),
                    Paragraph(Text(
                        "Mathlib has the adjugate and its 2x2 formula but no statement that conjugation by a "
                        + "specific square-root-of-(-3) matrix equals the adjugate iff trace-orthogonality, so this "
                        + "is a genuine biconditional, not a library restatement. It records only the algebraic "
                        + "linear constitution of residual E.72. The geometric axis biconditional (the rotation "
                        + "axis passing through the reference point), the class-level crossing criterion, the "
                        + "Sarnak reciprocity dictionary, and the Fricke bridge toward X0(3) are not covered."))),
                DescribeRole.Theorem
            )),
        []));
}
