using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Approximate;

internal sealed class RankOneCornerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact rank-one extension input gives a scalar Hilbert geometry on actual mixed corners.",
        H("The designated corner line and its scale"),
        Blocks(
            Paragraph(Text("Let H be any finite-dimensional complex Hilbert space with an additive conjugate-linear involution and the original continuous bilinear product mu. Its strict unit e has Hilbert norm one. Retain adjoint(L_x)=L_(star x), star(mu(x,y))=mu(star y,star x), M>=1, nonnegative delta, bilinear norm at most M and Hilbert associator bound delta times the input norms. Write p(x)=norm(L_x), r=tau+M delta, and use the actual corrected compression C(P,Q) and its range S_PQ. No multiplication instance or new Hilbert structure is imposed on H.")),
            Paragraph(Text("Assume Q is self-adjoint, tau>=0, p(mu(Q,Q)-Q)<=tau, r<=1/1024 and 520000 r M^2<=1. The conditional input is exactly finrank_C(S_QQ)=1, as in the one-dimensional projection antecedent of Kitaev, arXiv:2405.02434v2, section 7 and Lemma 9.4. The Q97.19-Q97.21 route in the same-scale product stability continuation uses that paper's global extension theorem. The local condition here does not select Q from the original product and does not establish an identification with a different old corner or its local matrix map.")),
            Describe.Lean(
                DescribeId.Create("actual-rank-one-scalar-geometry"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Approximate/RankOneCorner.rank_one_pairing_bounds"),
                H("Scalar coefficients, positivity and both scales"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every such original product and rank-one input, set t=C(Q,Q)Q. Then t is nonzero. The coordinate phi on S_QQ is normalized by phi(t)=1, and b(Y,X)=phi(C(Q,Q)mu(star Y,X)). Define beta=Re b(t,t) and alpha=Re inner(e,t). Both are strictly positive, and abs(beta-1)<=219140 r. For every self-adjoint P with p(mu(P,P)-P)<=tau and every X in S_PQ, b(X,X)t=C(Q,Q)mu(star X,X), b(X,X) is real nonnegative and vanishes exactly at X=0. Its Hilbert bounds are (1-260000 r M^2)norm(X)^2<=alpha b(X,X)<=(1+260000 r M^2)norm(X)^2. With d=delta+260000 r, its regular bounds are (1-d)p(X)^2<=b(X,X)p(t)<=(1+d)p(X)^2.")),
                    Paragraph(Text("The original product estimates give p(t-Q)<=9737 r, p(C(Q,Q)Z)<=5p(Z), and p(C(Q,Q)mu(t,X)-X)<=219140 r p(X) on S_QQ. The last constant times r is strictly less than one. The nonzero rank-one range therefore forces t to be nonzero. Unique scalar coordinates and star covariance give the coefficient equation and Hermitian symmetry. The same action estimate bounds beta away from zero; square nondegeneracy then makes alpha positive.")),
                    Paragraph(Text("The Hilbert estimates compare the compressed square with the actual square and use the original adjoint identity inner(e,mu(star X,X))=norm(X)^2. The passage from p(X) to the Hilbert norm costs M^2. The regular estimates instead use the operator C*-identity for L_X and the actual associator defect, giving (1-delta)p(X)^2<=p(mu(star X,X))<=(1+delta)p(X)^2. Neither comparison identifies the two original norms.")),
                    Paragraph(Text("The generator is literally t=C(Q,Q)Q throughout the coefficient equation. Its coefficient square beta is retained, rather than set equal to one. The scalar column with unit coefficient norm is c mapped to c t/sqrt(beta); c mapped to c t has squared coefficient norm beta times abs(c)^2. In particular, an approximate unit condition does not supply exact beta=1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-symmetric-corner-maps"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Approximate/RankOneCorner.symmetricCornerMaps"),
                H("The two adjoint directions of compressed multiplication"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all allowed self-adjoint P,R, every Z in S_PR and every X in S_RQ, Y in S_PQ, take F_Z(X)=C(P,Q)mu(Z,X) and G_Z(Y)=C(R,Q)mu(star Z,Y). In the Hilbert structures defined by b on separate corner types, h_PR(Z)=(F_Z+G_Z.adjoint)/2 and h_RP(star Z)=(G_Z+F_Z.adjoint)/2. The second map equals the first map's exact adjoint, and 2b(Y,h_PR(Z)X)=b(C(R,Q)mu(star Z,Y),X)+b(Y,C(P,Q)mu(Z,X)).")),Paragraph(Text("This is the symmetric actual compressed left action of the conditional extension route, with the order of the two scalar arguments preserved. Only the separate corner copies receive the coefficient Hilbert structure. Quantitative action error, multiplicative defect, dimension or saturation conclusions, the original selection of Q and the direct correction of a caller's old local matrix map remain additional obligations. No full Q97 or block-extension conclusion follows from these scalar and adjoint relations."))),
                DescribeRole.Definition))));
}
