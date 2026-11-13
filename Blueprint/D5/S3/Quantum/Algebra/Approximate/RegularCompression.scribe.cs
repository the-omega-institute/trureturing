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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-bracketing-closeness"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Approximate/RegularCompression.compression_closeness"),
                H("Closeness to both actual bracketings"),
                StatementSource.FromAuthor(Disp(Seq(Call("p", Seq(Call("C", F.Id("P"), F.Id("Q"), F.Id("x")), Minus, Call("mu", F.Id("P"), Call("mu", F.Id("x"), F.Id("Q"))))), Le, Multiply(Multiply(Seq(D(4), D(8), D(6), D(6)), Seq(Tau, Plus, F.Id("M"), DeltaLower)), Call("p", F.Id("x")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let r=tau+M delta. For self-adjoint P and Q, nonnegative tau, r at most 1/1024, and actual p-projection defects at most tau, both p(C(P,Q)x-mu(P,mu(x,Q))) and p(C(P,Q)x-mu(mu(P,x),Q)) are at most 4866 r p(x), for every x. The Taylor tail is at most the square defect, hence at most 512 r. The midpoint displacement is at most 4864 r and the actual commutator contributes at most 2 r for either bracketing."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-bracketing-hilbert"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Approximate/RegularCompression.compression_closeness_hilbert"),
                H("The original Hilbert operator bounds"),
                StatementSource.FromAuthor(Disp(Seq(Call("norm", Seq(Call("C", F.Id("P"), F.Id("Q")), Minus, Multiply(Call("L", F.Id("P")), Call("R", F.Id("Q"))))), Le, Multiply(Multiply(Seq(D(4), D(8), D(6), D(6)), Seq(Tau, Plus, F.Id("M"), DeltaLower)), F.Id("M"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under exactly the same self-adjointness, nonnegative tau, r at most 1/1024 and actual p-projection-defect hypotheses, both Hilbert operator norms of C(P,Q)-L_P R_Q and C(P,Q)-R_Q L_P are at most 4866 M r. The additional M comes from norm(x) at most p(x) at most M norm(x). The regular and original Hilbert operator norms are not identified."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-compression-star"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Approximate/RegularCompression.compression_star"),
                H("Star exchanges the actual corner labels"),
                StatementSource.FromAuthor(Disp(Seq(Call("star", Call("C", F.Id("P"), F.Id("Q"), F.Id("x"))), Eq, Call("C", F.Id("Q"), F.Id("P"), Call("star", F.Id("x")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same hypotheses, star(C(P,Q)x)=C(Q,P)(star(x)) for every x. The actual star reversal interchanges left and right multiplication. Its p-isometry gives a bounded real-linear involution on the regular range, and the convergent Taylor correction preserves this intertwining. This is star covariance, with no assertion that a mixed compression is positive or an orthogonal projection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-complement-two-piece"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Approximate/RegularCompression.compression_two_piece"),
                H("The actual complementary two-piece decomposition"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("p", Seq(Call("C", F.Id("P"), F.Id("Q"), F.Id("x")),
                        Plus, Call("C", F.Id("P"), Seq(F.Id("e"), Minus, F.Id("Q")), F.Id("x")),
                        Minus, Call("C", F.Id("P"), F.Id("e"), F.Id("x")))),
                    Le, Multiply(Multiply(Seq(D(1), D(4), D(5), D(9), D(8)),
                        Seq(Tau, Plus, F.Id("M"), DeltaLower)), Call("p", F.Id("x")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same hypotheses, p(C(P,Q)x+C(P,e-Q)x-C(P,e)x) is at most 14598 r p(x), for every x. The actual unit is star fixed, e-Q has exactly the same projection defect as Q, and the uncorrected bracketings add exactly. Applying the three quantitative compression bounds gives the decomposition error. This does not identify the two corrected ranges as an exact direct sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compatible-corner-product-support"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Approximate/RegularCompression.corner_product_support"),
                H("The actual compatible-corner product has approximate outer support"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("p", Seq(Call("C", F.Id("P"), F.Id("R"),
                        Call("mu", F.Id("x"), F.Id("y"))), Minus,
                        Call("mu", F.Id("x"), F.Id("y")))), Le,
                    Multiply(Multiply(Multiply(Seq(D(2), D(6), D(0), D(0), D(0), D(0)),
                        Seq(Open, Tau, Plus, F.Id("M"), DeltaLower, Close)), Call("p", F.Id("x"))),
                        Call("p", F.Id("y")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For the same original finite-dimensional complex Hilbert product, let P, Q and R be self-adjoint, let tau be nonnegative, set r=tau+M delta, assume r at most 1/1024, and bound all three actual p-projection defects by tau. For every x in range C(P,Q) and y in range C(Q,R), the displayed estimate holds with the universal numerical constant 260000. No orthogonality of the labels, exact corner closure, associativity of H, scalar pairing, or saturation is assumed.")),
                    Paragraph(Text("Exact idempotence makes x fixed by C(P,Q). The bracketing estimate and the original associator bound imply p(mu(P,x)-x) at most 24354 r p(x). Star reversal gives the corresponding right support bound for y and R. The product estimate p(mu(a,b)) at most 2 p(a)p(b), valid at this scale, then controls the five differences through mu(P,mu(mu(x,y),R)), mu(P,mu(x,mu(y,R))), mu(P,mu(x,y)), and mu(mu(P,x),y). Their coefficients sum to 253282, bounded by 260000. M enters only through r in this regular-norm estimate. The result is approximate product support; exact closure, minimal-corner scalar pairing, positivity, dimension transfer and column saturation require further arguments."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-corner-square-nondegeneracy"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Approximate/RegularCompression.corner_square_nondegenerate"),
                H("The actual compressed square detects nonzero mixed-corner vectors"),
                StatementSource.FromAuthor(Disp(Seq(
                    new Formula.Fraction(Seq(Call("norm", F.Id("x")), Caret, Grp(D(2))), D(2)),
                    Le, Call("Re", Call("inner", F.Id("e"),
                        Call("C", F.Id("Q"), F.Id("Q"),
                            Call("mu", Seq(F.Id("x"), Caret, Grp(Star)), F.Id("x")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Retain the same original Hilbert product and all the self-adjointness, projection-defect, nonnegative-tau and r at most 1/1024 hypotheses for P and Q. If additionally 520000 r M^2 is at most one, then every x in range C(P,Q) satisfies the displayed lower bound, and C(Q,Q)mu(star(x),x)=0 if and only if x=0. The norm here is the original Hilbert norm, and e is the original strict unit of Hilbert norm one.")),
                    Paragraph(Text("Star reversal places star(x) in the reversed actual corner. Applying the compatible-corner support estimate bounds the p-distance of the compressed square from the original square by 260000 r p(x)^2. The original adjoint law and strict right unit give exactly inner(e,mu(star(x),x))=inner(x,x). Cauchy-Schwarz bounds the expectation error by the same regular-norm error. The comparison p(x) at most M norm(x) gives the stated half-norm lower bound at the additional scale, and hence detects zero exactly. The M^2 factor is explicit; no M-independent Hilbert positivity radius is asserted. This result does not define the scalar coefficient b(Y,X)t_Q, prove that the actual diagonal corner is one-dimensional, or establish column saturation or a block extension."))),
                DescribeRole.Theorem))));
}
