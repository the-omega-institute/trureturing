using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Approximate;

internal sealed class RegularCompressionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original nonassociative Hilbert-space product defines an exact compression in its regular-action norm.",
        H("Compression from the original regular actions"),
        Blocks(
            Paragraph(Text("Let H be any finite-dimensional complex Hilbert space with a conjugate-linear additive involution. The data consist of the original continuous complex-bilinear product mu, its strict two-sided unit e with Hilbert norm one, the reversal identity for the involution, and the Hilbert-adjoint identity adjoint(L_x)=L_(star x). Assume the bilinear norm is at most M, M is at least one, and the original Hilbert associator norm is at most delta times the three input norms, with delta nonnegative.")),
            Paragraph(Text("Define p(x) as the original Hilbert operator norm of L_x. The auxiliary Banach space is the range of x mapped to L_x, with the inherited operator norm. Evaluation at e proves injectivity and identifies H linearly and continuously with this range. Actual left and right multiplication are transported through this identification. For P and Q, set T=L_P R_Q+R_Q L_P-identity and let C(P,Q) be the transport to H of one half of the sum of identity and T times the Taylor inverse-square-root series evaluated at T squared minus identity. No associative multiplication or C*-algebra instance is added to H, and the Hilbert structure on H is retained.")),
            Describe.Lean(
                DescribeId.Create("original-regular-compression-idempotent"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Approximate/RegularCompression.compression_idempotent"),
                H("Exact idempotence from the actual product defects"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("P"), Comma, F.Id("Q"), InMacro, Sp, F.Id("H"),
                    Comma, Sp, Forall, Sp, Tau, Sp, InMacro, Sp, Seq(Mathbb, Grp(F.Id("R"))), Comma, Sp,
                    F.Id("P"), Caret, Grp(Star), Eq, F.Id("P"), Comma, Sp,
                    F.Id("Q"), Caret, Grp(Star), Eq, F.Id("Q"), Comma, Sp,
                    D(0), Le, Sp, Tau, Comma, Sp,
                    Tau, Plus, F.Id("M"), Sp, DeltaLower, Sp, Le, Sp,
                    new Formula.Fraction(D(1), Seq(D(1), D(0), D(2), D(4))), Comma, Sp,
                    Call("p", Seq(Call("mu", F.Id("P"), F.Id("P")), Minus, F.Id("P"))),
                    Le, Sp, Tau, Comma, Sp,
                    Call("p", Seq(Call("mu", F.Id("Q"), F.Id("Q")), Minus, F.Id("Q"))),
                    Le, Sp, Tau, Sp, Implies, Sp,
                    Call("C", F.Id("P"), F.Id("Q")), Caret, Grp(D(2)), Eq,
                    Call("C", F.Id("P"), F.Id("Q"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For self-adjoint P and Q with p(mu(P,P)-P) and p(mu(Q,Q)-Q) at most tau, assume tau is nonnegative and tau+M delta is at most 1/1024. The norm of the square of T=L_P R_Q+R_Q L_P-identity minus identity is at most 512(tau+M delta) in the auxiliary operator algebra. Thus the inverse-square-root Taylor series converges. One half of the sum of identity and T times that series is exactly idempotent, and conjugation by the regular-range equivalence gives an exactly idempotent continuous linear map on the original H.")),
                    Paragraph(Text("The approximate-projection bounds, left/right square defects and commutator defect are derived from mu. The mixed corner is defined as the range of this corrected map. The construction follows Kitaev, Almost-idempotent quantum channels and approximate C*-algebras, arXiv:2405.02434v2, sections 3 and 7. It is a prerequisite for the full-corner construction of Lemma 9.4; it does not establish corner saturation, an exact matrix action, compatible columns, or the block extension."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-regular-star-reversal"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Approximate/RegularCompression.p_star_mul_rev"),
                H("The regular norm respects star reversal"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), InMacro, Sp, F.Id("H"), Comma, Sp,
                    Call("p", Call("mu", Seq(F.Id("y"), Caret, Grp(Star)),
                        Seq(F.Id("x"), Caret, Grp(Star)))), Eq, Sp,
                    Call("p", Call("mu", F.Id("x"), F.Id("y"))), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The equality is obtained from the original involution reversal law and "
                        + "adjoint invariance of the operator norm. It is used by the transported "
                        + "right-action estimates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-regular-two-piece-defects"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Approximate/RegularCompression.two_piece_defects"),
                H("The two actual regular actions have controlled defects"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("P"), Comma, Sp, F.Id("Q"), InMacro, Sp, F.Id("H"), Comma, Sp,
                    Forall, Sp, Tau, Sp, InMacro, Sp, Seq(Mathbb, Grp(F.Id("R"))), Comma, Sp,
                    D(0), Le, Sp, Tau, Comma, Sp,
                    Call("p", Seq(Call("mu", F.Id("P"), F.Id("P")), Minus, F.Id("P"))),
                    Le, Sp, Tau, Comma, Sp,
                    Call("p", Seq(Call("mu", F.Id("Q"), F.Id("Q")), Minus, F.Id("Q"))),
                    Le, Sp, Tau, Sp, Implies, Sp,
                    Open,
                    Call("norm", Seq(Call("left", F.Id("P")), Star, Call("left", F.Id("P")), Minus,
                        Call("left", F.Id("P")))), Le, Sp,
                    Seq(F.Id("M"), Sp, DeltaLower, Sp, Call("p", F.Id("P")), Caret, Grp(D(2)),
                        Plus, Seq(Open, D(1), Plus, DeltaLower, Close), Sp, Tau), Sp, Land, Sp,
                    Call("norm", Seq(Call("right", F.Id("Q")), Star, Call("right", F.Id("Q")), Minus,
                        Call("right", F.Id("Q")))), Le, Sp,
                    Seq(F.Id("M"), Sp, DeltaLower, Sp, Call("p", F.Id("Q")), Caret, Grp(D(2)),
                        Plus, Seq(Open, D(1), Plus, DeltaLower, Close), Sp, Tau), Sp, Land, Sp,
                    Call("norm", Seq(Call("left", F.Id("P")), Star, Call("right", F.Id("Q")), Minus,
                        Call("right", F.Id("Q")), Star, Call("left", F.Id("P")))), Le, Sp,
                    Seq(F.Id("M"), Sp, DeltaLower, Sp, Call("p", F.Id("P")), Sp, Call("p", F.Id("Q"))), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonnegative tau and actual p-defects of P and Q bounded by tau, the "
                        + "left and right transported actions have square defects bounded by "
                        + "M delta p(P)^2 plus (1+delta) tau and M delta p(Q)^2 plus "
                        + "(1+delta) tau. Their commutator is bounded by M delta p(P)p(Q). "
                        + "All three estimates are derived from the same original product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-regular-compression-closeness"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Approximate/RegularCompression.regularCompression_closeness"),
                H("The actual compression is close to its midpoint"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("P"), Comma, Sp, F.Id("Q"), InMacro, Sp, F.Id("H"), Comma, Sp,
                    Forall, Sp, Tau, Sp, InMacro, Sp, Seq(Mathbb, Grp(F.Id("R"))), Comma, Sp,
                    F.Id("P"), Caret, Grp(Star), Eq, F.Id("P"), Comma, Sp,
                    F.Id("Q"), Caret, Grp(Star), Eq, F.Id("Q"), Comma, Sp,
                    D(0), Le, Sp, Tau, Comma, Sp,
                    Tau, Plus, F.Id("M"), Sp, DeltaLower, Le, Sp,
                    new Formula.Fraction(D(1), Seq(D(1), D(0), D(2), D(4))), Comma, Sp,
                    Call("p", Seq(Call("mu", F.Id("P"), F.Id("P")), Minus, F.Id("P"))),
                    Le, Sp, Tau, Comma, Sp,
                    Call("p", Seq(Call("mu", F.Id("Q"), F.Id("Q")), Minus, F.Id("Q"))),
                    Le, Sp, Tau, Sp, Implies, Sp,
                    Call("norm", Seq(Call("regularCompression", F.Id("P"), F.Id("Q")), Minus,
                        Multiply(new Formula.Fraction(D(1), D(2)),
                            Seq(Open, D(1), Plus, Call("cornerInvolution", F.Id("P"), F.Id("Q")), Close)))),
                    Le, Sp, Multiply(new Formula.Fraction(Seq(D(1), D(9)), D(2)),
                        Call("norm", Seq(Call("inverseSqrt", Seq(
                            Call("cornerInvolution", F.Id("P"), F.Id("Q")), Caret,
                            Grp(D(2)), Minus, D(1))), Minus, D(1)))), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the stated self-adjointness, p-defect, nonnegativity and smallness "
                        + "conditions, the norm of the actual corner involution is at most 19. "
                        + "The generic Taylor-tail estimate therefore gives the displayed "
                        + "quantitative midpoint bound for the same original-product compression."))),
                DescribeRole.Theorem))));
}
