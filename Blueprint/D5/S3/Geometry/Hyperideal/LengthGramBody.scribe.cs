using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LengthGramBodyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The common six-length cut body has a Lorentz and upper-half-space coordinate realization.",
        H("One shared body from the actual length Gram matrix"),
        Blocks(
            Paragraph(Text("Let l be six positive real lengths in the order "
                + "(01,02,03,23,13,12). The symmetric matrix G has diagonal entries "
                + "one and off-diagonal entries minus cosh of the corresponding length. "
                + "The set C consists of nonnegative four-coordinate vectors whose "
                + "coordinates sum to one and whose four G-row values are nonpositive. "
                + "Write q(v)=v-transpose G v, r(v)=v/sqrt(-q(v)), and "
                + "b=(1/4,1/4,1/4,1/4). R6 and R4 denote real coordinate spaces. "
                + "B is the Lorentz form with signs (+,+,+,-). The function phi01 "
                + "is the original six-variable cosine formula applied to cosh(l). "
                + "For a future unit timelike y, Psi(y) has horizontal coordinate "
                + "(y0+i*y1)/(y3-y2) and height 1/(y3-y2). H3 denotes the "
                + "repository's HyperbolicThreeSpace with its actual metric topology.")),
            Describe.Lean(
                DescribeId.Create("six-length-shared-radial-body"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/LengthGramBody.shared_radial_body"),
                H("Compactness, explicit frame and shared coordinate map"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The barycenter strictly satisfies every cut. "
                        + "A cut equality at a positive coordinate forces that coordinate "
                        + "to exceed one half. If q vanished, every positive coordinate "
                        + "would require a cut equality. Two positive coordinates cannot "
                        + "both exceed one half, while a singleton support violates its "
                        + "own cut. Thus q is strictly negative throughout the same C.")),
                    Paragraph(Text("The positive square-root denominator makes r "
                        + "continuous. The sum of the image coordinates recovers its "
                        + "reciprocal scale, so r is injective. Its image is compact "
                        + "and nonempty, and the quadratic value there equals minus one.")),
                    Paragraph(Text("The strict condition on phi01 makes the final "
                        + "square root in the explicit four-vector frame positive. "
                        + "The frame's Lorentz Gram is exactly G and its determinant "
                        + "is positive. Congruence with diag(1,1,1,-1) gives det(G)<0. "
                        + "Every point of the same radial body is future unit timelike. "
                        + "Its positive denominator y3-y2 defines Psi throughout C. "
                        + "The coordinate inverse proves injectivity, and the existing "
                        + "coordinate homeomorphism proves continuity into actual H3.")),
                    Paragraph(Text("This closes the shared compact coordinate-body "
                        + "and frame step of the original six-length construction. "
                        + "It does not yet assert three-dimensional interior, complete "
                        + "triangular/hexagonal incidence, geodesic intervals, prescribed "
                        + "edge distances, dihedral angles or relabeling isometries. "
                        + "Those obligations retain the original all-six strict source "
                        + "cosine domain; one strict condition suffices for this frame step.")),
                    Paragraph(Text("Application: a smooth native-coordinate family anchored at the entire original frame. Fix six positive lengths l0, an invertible original frame M0 with G(l0)=M0*J*transpose(M0), and an original radial realization f0 on the complete closed C(l0), where J=diag(1,1,1,-1). Put H(l)=inverse(M0)*G(l)*transpose(inverse(M0)). Then H(l0)=J. The construction below preserves every entry of M0 at the base parameter.")),
                    Paragraph(Text("For a symmetric H define r0=H00 and c00=sqrt(r0); c10=H10/c00, c20=H20/c00, c30=H30/c00. Next set r1=H11-c10^2, c11=sqrt(r1), c21=(H21-c20*c10)/c11, c31=(H31-c30*c10)/c11. Set r2=H22-c20^2-c21^2, c22=sqrt(r2), c32=(H32-c30*c20-c31*c21)/c22. Finally set r3=-H33+c30^2+c31^2+c32^2 and c33=sqrt(r3). Let C(H) be the lower triangular matrix with these entries and zeros above the diagonal. All four r are one at J. On their positive domain the ten scalar equations give C(H)*J*transpose(C(H))=H and det(C(H))>0. This is the signed Cholesky construction; the last radicand uses the negative coordinate of J.")),
                    Paragraph(Text("Positive square roots and nonzero denominators make every entry smooth on this open domain. Thus M(l)=M0*C(H(l)) is smooth on an open neighborhood of l0 within positive lengths, has nonzero determinant, satisfies M(l)*J*transpose(M(l))=G(l), and obeys M(l0)=M0 exactly. Constant inverse cancellation proves the Gram identity; no smoothness of a separately selected frame is assumed.")),
                    Paragraph(Text("For the joint native map put U(l,v)=v times M(l), Q(l,v)=U3^2-U0^2-U1^2-U2^2 and d(l,v)=U3-U2, and define F(l,v)=(U0/d,U1/d,sqrt(Q)/d). The supplied original future-unit radial contract gives Q(l0,v)>0 and d(l0,v)>0 at every v in the full C(l0). The same contract identifies F(l0,v) with the native coordinates of f0(v), including every face, edge and vertex. The joint set where the four frame radicands, Q and d are positive is open, and F is smooth there.")),
                    Paragraph(Text("Compactness of the entire original C(l0), together with the generalized tube lemma, gives open A around l0 and open B containing C(l0) such that A times B lies in this joint positive domain. The actual moving cut bodies stay in B after shrinking A. To see this, use the fixed compact standard simplex: a point in B remains in B locally, while a point outside B must violate some original G-row inequality strictly at l0, and that violation persists nearby. Compactness makes this implication uniform. This proves containment of every point of C(l), including its boundary; it does not infer containment from moving vertices alone.")),
                    Paragraph(Text("Consequently one common open product supports the same anchored smooth F and contains every nearby complete moving C(l), while all nearby frames retain their exact Gram identity and nonzero determinant. This constructs a family through the prescribed f0 in native coordinates. It does not assert smoothness of arbitrary independently supplied realizations at other parameters. Moving-volume differentiation and the Schlaefli formula require their transport and boundary-flux arguments in addition to this family.")),
                    Paragraph(Text("Application: the frame-induced continuity equation for the original Gram density. Use the affine chart a(x)=(x0,x1,x2,1-x0-x1-x2), with its last coordinate recovered from the sum-one constraint. This is the chart used in the original twenty-cell and face-flux calculations. It differs from the first-coordinate-recovered chart in the volume integral below; the two coordinate conventions are kept explicit. Let M(s) be a real differentiable frame path, D its derivative at t, and det(M(t)) nonzero. Set K=D*inverse(M(t)), U=a(x)*M(t), Q=-B(U,U), and rho=abs(det(M(t)))/Q^2. The pointwise calculation requires Q nonzero; the native geometric interpretation uses Q positive.")),
                    Paragraph(Text("Write u=a(x)*K, alpha=sum_i(u_i), and W_i=u_i-alpha*x_i for i=0,1,2. The sum-zero lift of W is a(x)*K-alpha*a(x). Since K*M(t)=D, its image under the original frame is a(x)*D-alpha*U. Consequently the spatial directional derivative of Q along W equals its frame-time derivative minus 2*alpha*Q. These equations retain the row-vector convention of the original Gram realization.")),
                    Paragraph(Text("Differentiation of the four determinant rows, using the existing alternating determinant derivative and Matrix.det_updateRow_sum, gives d/ds abs(det(M(s))) at t equal to abs(det(M(t)))*trace(K), for either determinant sign. Direct differentiation in the three displayed affine coordinates gives div(W)=trace(K)-4*alpha. Here div(V) is the sum of the three coordinate derivatives of V_i. Product and quotient differentiation then give the positive-sign identity "),
                        Text("partial_t rho = div(rho*W)"),
                        Text(". Indeed grad(Q) dot W=partial_t(Q)-2*alpha*Q, so the two alpha terms in div(rho*W) cancel exactly. This is a local pointwise derivative identity; it needs neither integration over a cell nor a boundary regularity assumption.")),
                    Paragraph(Text("If the same path satisfies B(M(s)_i,M(s)_j)=G(l(s))_ij throughout a neighborhood of t, the existing original-frame determinant and quadratic identities give abs(det(M(s)))=sqrt(-det(G(l(s)))) and Q(s,x)=-a(x)*G(l(s))*transpose(a(x)). Thus rho is exactly the original Gram coefficient density in this last-coordinate chart. Equality on the full parameter neighborhood transfers the time derivative to that original density, and equality for every spatial x at t transfers the divergence. The pointwise identity holds for every spatial x where the quadratic denominator is nonzero, without imposing positive frame orientation.")),
                    Paragraph(Text("This application supplies the coefficient-density part of moving-volume transport. Uniform bounds for differentiation under the integral and combination with the moving-cell and original face-flux formulas remain to be established. The displayed pointwise equation alone does not assert a derivative of the measured native-body volume or the Schlaefli formula.")),
                    Paragraph(Text("Application: native frame velocity along the actual length path. Retain the last-coordinate-recovered chart a(x)=(x0,x1,x2,1-x0-x1-x2). For U=a(x)M put Q=-B(U,U), d=U3-U2 and N(U)=(U0/d,U1/d,sqrt(Q)/d). At Q>0 and d nonzero, the actual coordinate differential DN_U annihilates the radial direction U. For a differentiable frame path M(s), with det(M(t)) nonzero, D=M′(t), K=D M(t)^(-1) and W(x)=(a(x)K)_first3-(a(x)K 1)x, the sum-zero lift of W obeys tangent(W) M(t)=a(x)D-(a(x)K 1)U. Applying DN_U therefore proves that the time derivative of N(a(x)M(s)) at t equals the spatial directional derivative of N(a(x+rW(x))M(t)) at r=0. This identifies the displayed positive frame-motion field with the velocity of the actual native coordinates; it does not require a choice of positive frame determinant.")),
                    Paragraph(Text("This identification applies to a genuine path through any prescribed original realization. Fix six positive lengths l0, an invertible original frame M0 with M0 J M0-transpose=G(l0), and the same original radial-coordinate map f on the full closed cutBody(l0). For a real length path l(s) differentiable at t with l(t)=l0, use the already constructed smooth anchored frame P(s)=frame(M0,l(s)). Its derivative is D=(D_l frame(M0,l0))[l′(t)], and P(t)=M0. Openness of the frame-construction domain supplies the Gram identity on one full time neighborhood, so the preceding original-density continuity equation applies to this same P. For every x whose a(x) belongs to the full closed original cut body, the original future radial-coordinate contract supplies Q>0 and d>0, and N(a(x)P(t)) is exactly the coordinate triple of f(a(x)). Both the density derivative and the native frame-velocity identification consequently hold at each such point, including the cut boundary, with the same D and W.")),
                    Paragraph(Text("These are pointwise identities for the original length path and realization. They do not yet differentiate a moving affine cell, interchange a derivative with its integral, identify a native moving-volume derivative, or establish the Schlaefli identity. Those steps require the moving-cell velocity, common-neighborhood bounds and the separate geometric flux bridge.")),
                    Paragraph(Text("Application: total native velocity for a moving coefficient point. In the same last-coordinate chart, let both x(s) and M(s) be differentiable at t, with v=x′(t), D=M′(t), det(M(t)) nonzero, Q(t,x(t))>0 and d(t,x(t)) nonzero. The coefficient lift has derivative tangent(v), so the ambient row x(s) lifted and multiplied by M(s) has derivative tangent(v) M(t)+a(x(t))D. Write F(s,z)=N(a(z)M(s)). The radial-null identity for DN therefore gives d/ds F(s,x(s)) at t = d/dr F(t,x(t)+r*(v+W(x(t)))) at r=0. Thus the actual native velocity is the image of the sum v+W under the fixed-frame spatial differential. This is valid for either nonzero frame orientation and applies to a genuine moving point; the original-cell derivatives and their anchored realization correspondence are supplied below.")),
                    Paragraph(Text("For a fixed invertible real 3-by-3 matrix A, offset b and vector field H differentiable at b+A*u with derivative L, set j=abs(det(A)) and P(u)=j*A^(-1)*H(b+A*u). The chain rule gives DP(u)=j*A^(-1)*L*A. In the coordinate convention div(H)=trace(DH), trace cyclicity and A*A^(-1)=I give div_u(P)(u)=j*div_x(H)(b+A*u). This static affine Piola identity preserves the absolute cell determinant, so it imposes no positive-orientation convention on A. It needs only the displayed first derivative of H at the image point.")),
                    Paragraph(Text("The moving-point velocity, the original twenty-cell path derivatives, and affine transport with a joint time-dependent density are now available. Their application to the actual native-volume integral still requires joint differentiability and flux assembly for the original frame density, a common parameter neighborhood and uniform bounds, and the integral and boundary-flux identifications. Schlaefli remains a separate obligation.")),
                    Paragraph(Text("Application: differentiating the original twenty moving cells. Let l(s) retain the six independent lengths in the order 01,02,03,23,13,12, and let V(n,j,l) be the literal ordered vertex table of the existing twenty-cell decomposition, with n in Fin 20 and j in Fin 4. In the last-coordinate-recovered chart, write o_n(l)=drop(V(n,0,l)) and let column i of B_n(l) be drop(V(n,i+1,l))-o_n(l). The actual affine cell point is a_n(l,u)=o_n(l)+B_n(l)u. Every endpoint entry is zero or a quotient with numerator 1 or cosh(l_e) and denominator 1+cosh(l_e). The denominator is positive for every real input. The chain rule and the finite vertex table therefore give differentiability of every actual endpoint, every V(n,j,l(s)), every B_n(l(s)), and every a_n(l(s),u) whenever the six-length path is differentiable at the evaluation time. No independent vertex-velocity hypothesis is introduced.")),
                    Paragraph(Text("Let Delta={u in R3: each u_i>=0 and sum_i u_i<=1}, including its boundary. Its barycentric weights are (1-sum_i u_i,u0,u1,u2), in exactly the original vertex order. For six positive base lengths, convexity and membership of the four original cell vertices put c_n(l,u)=sum_j weight_j(u)V(n,j,l) in the same original cut body C(l). The sum of its four coordinates is one. Thus drop(c_n)=a_n and the sum-one lift of a_n is c_n. This identifies the affine point with an actual coefficient point of the original body for every one of the twenty cells, including all reference faces, edges and vertices. The previously established nonzero determinant of each original B_n applies at every such positive-length base parameter.")),
                    Paragraph(Text("For the same base lengths l0, invertible Gram frame M0 and original radial realization f0 used in the anchored frame construction, take M(s)=frame(M0,l(s)) and l(t)=l0. For any n and fixed u in the closed Delta, put x=a_n(l0,u), v=d/ds a_n(l(s),u) at t, D=M′(t), and K=D inverse(M0). The point x lifted to four coefficients lies in C(l0). Applying the original future-unit radial-coordinate contract to that very point gives Q(M0,x)>0, d(M0,x)>0 and N(a(x)M0)=nativeCoordinates(f0(a(x))). These are consequences of the given original realization, rather than extra positivity assumptions on a replacement map.")),
                    Paragraph(Text("The anchored frame derivative and the preceding actual cell derivative now give d/ds N(a(a_n(l(s),u))M(s)) at t = d/dr N(a(x+r*(v+W_K(x)))M0) at r=0. Here a is the sum-one lift and W_K is the same positive projective frame-motion field as above. This is the total native velocity at every fixed reference point of every original cell; its base value is the coordinate of the same original f0. The conclusion is pointwise at t and does not package a realization family with native codomain on a whole parameter neighborhood.")),
                    Paragraph(Text("Application: affine transport with a genuinely time-dependent density. For a differentiable origin o(s), a differentiable invertible three-by-three matrix B(s), and fixed u, put x(s,u)=o(s)+B(s)u, v=o′(t), E=B′(t), j=abs(det(B(t))), and x=x(t,u). Suppose rho(s,z) has a joint Frechet derivative L at (t,x). Define partial_t rho=L(1,0) and D_x rho[w]=L(0,w). The chain rule gives d/ds rho(s,x(s,u)) at t = partial_t rho+D_x rho[v+Eu]. The absolute-determinant derivative is j*trace(inverse(B(t))*E); it uses nonzero det(B(t)) and applies to either orientation.")),
                    Paragraph(Text("For the coordinate divergence in u, the resulting exact identity is d/ds [abs(det(B(s)))*rho(s,x(s,u))] at t = j*partial_t rho + div_u P(u), where P(u)=j*rho(t,o(t)+B(t)u)*inverse(B(t))*(v+Eu). Differentiate each coordinate of P along the corresponding reference basis line. After extracting the common factor j, the density terms sum to D_x rho[v+Eu] because B(t)*inverse(B(t))=I, while the velocity terms sum to rho*trace(inverse(B(t))*E). This proves the displayed formula with the actual absolute determinant and the joint time-space derivative. It supplies the affine transport step; substituting the original frame density and combining its continuity equation with static affine Piola still requires the corresponding joint differentiability and flux assembly.")),
                    Paragraph(Text("For the original volume calculation, retain all six positive lengths and all "
                        + "six strict source cosines, and fix any original witnesses M and f satisfying the "
                        + "displayed frame and radial-coordinate equations. Use EuclideanSpace Real (Fin 3) "
                        + "with its L2 norm and canonical three-dimensional Haar volume. Set "
                        + "A(u)=(1-u0-u1-u2,u0,u1,u2), D=A inverse-image C, X=A(u) times M, "
                        + "s=sqrt(-q(A(u))) and d=X3-X2. The sum-one condition on C proves A(D)=C: "
                        + "the inverse chart is P(v)=(v1,v2,v3). The same future unit timelike "
                        + "radial vector is Y=X/s, so s>0 and d=s*(Y3-Y2)>0 on all of D. "
                        + "Consequently the actual coordinates of f(A(u)) are (F0+i*F1,F2), where "
                        + "F(u)=(X0/d,X1/d,s/d). This identifies the literal original map, including "
                        + "all cut-boundary points; no alternate frame or body is selected.")),
                    Paragraph(Text("The Frechet derivative rules give the ambient derivative of this F "
                        + "where q(A(u))<0 and d is nonzero. For h in Real3, put "
                        + "v=(-h0-h1-h2,h0,h1,h2), w=v times M and delta=w3-w2. "
                        + "Then Ds[h]=-B(X,w)/s, and the derivative is "
                        + "DF[h]=(w0/d-X0*delta/d^2, w1/d-X1*delta/d^2, "
                        + "-B(X,w)/(s*d)-s*delta/d^2). This is an actual derivative of the "
                        + "coordinate function. Its restriction supplies a derivative within D "
                        + "even where a cut equality is active; boundary smoothness is unnecessary.")),
                    Paragraph(Text("The same coordinate differential has an exact Lorentz interpretation. "
                        + "For an ambient four-vector w set T_X(w)=w/s+B(X,w)*X/s^3, with "
                        + "s^2=-B(X,X). Differentiating the existing native lift L at the actual "
                        + "point F gives DL_F(DF[h])=T_X(w), where w=v times M as above. "
                        + "This identity is computed from the displayed coordinate functions; it "
                        + "does not assume an intertwining relation between two unknown derivatives. "
                        + "The same lift differential satisfies B(DL_F(a),DL_F(b))=(a dot b)/F2^2. "
                        + "Consequently, for w=v times M and z=v' times M, the original coordinate "
                        + "differential obeys (DF[h] dot DF[k])/F2^2=B(w,z)/s^2+"
                        + "B(X,w)*B(X,z)/s^4. Here v and v' are the original sum-zero coefficient "
                        + "directions determined by h and k.")),
                    Paragraph(Text("The actual sum-one section gives injectivity of the coordinate differential "
                        + "DN_X for N(X)=(X0/d,X1/d,s/d). Define "
                        + "S_M(Y)=sum_i((Y times inverse(M))_i). Frame invertibility gives "
                        + "S_M(X)=1 and S_M(w)=0 for every sum-zero coefficient direction. "
                        + "If DN_X(w)=0, the lift identity gives s^-1*w+a*X=0, where "
                        + "a=B(X,w)/s^3. Applying S_M forces a=0, then w=0; invertibility of M "
                        + "forces the coefficient direction to be zero. Thus every nonzero "
                        + "sum-zero direction has strictly positive displayed self-pairing. "
                        + "This proves positivity on the original three-dimensional section.")),
                    Paragraph(Text("The coordinate pairing also describes the first-order behavior of the "
                        + "unchanged native distance. Let gamma(t) be any curve in the actual upper "
                        + "half-space whose ambient Complex-times-Real coordinates have derivative V "
                        + "at zero, and write p=gamma(0). The ambient space here is WithLp 2, with "
                        + "its genuine L2 norm. The native distance formula is "
                        + "2*arsinh(D(t)/(2*sqrt(height(p)*height(gamma(t))))), where D(t) is the "
                        + "ambient distance. The derivative supplies D(t)/abs(t) tending to norm(V). "
                        + "Extend arsinh(x)/x continuously at zero by the value one, using its "
                        + "derivative there. Multiplying this continuous ratio by the preceding "
                        + "difference-quotient norm and the reciprocal height factor proves that "
                        + "dist_H(p,gamma(t))/abs(t) tends to norm(V)/height(p). This includes "
                        + "zero velocity and repeated curve points; no nonzero-image assumption is used.")),
                    Paragraph(Text("Packing a real triple a into (Complex.mk(a0,a1),a2) in WithLp 2 "
                        + "gives norm(pack(a))^2=a0^2+a1^2+a2^2=a dot a. This explicit identity "
                        + "supplies the Euclidean meaning of the coordinate pairing; the default "
                        + "sup norm on Fin 3 to Real is not identified with this L2 norm. "
                        + "For the same original xi in C and any coefficient direction eta, "
                        + "use N((xi+t*eta) times M) as the local coordinate extension. Its "
                        + "height stays positive near zero by continuity and the already derived "
                        + "s,d>0. Packing these coordinates gives a curve based at exactly f(xi). "
                        + "For all sufficiently small t for which xi+t*eta belongs to C, this same "
                        + "curve is exactly f(xi+t*eta), by the original radial-coordinate contract. "
                        + "The squared native distance quotient along it tends to "
                        + "B(w,w)/s^2+B(X,w)^2/s^4, with X=xi times M and w=eta times M. "
                        + "For nonzero eta with sum eta_i=0 this limit is strictly positive by "
                        + "the section argument. At a cut boundary this is an ambient differentiable "
                        + "coordinate extension; a two-sided curve contained in C is not required or asserted.")),
                    Paragraph(Text("These differential and metric-speed identities retain the same original "
                        + "frame, body, native distance and radial map, including their boundary-point "
                        + "coordinate identification. They do not yet identify an outward unit normal "
                        + "or transport a varying vector field against native surface measure. "
                        + "The weighted face-flux identity, moving measured-volume derivative and "
                        + "Schlaefli variation remain separate obligations.")),
                    Paragraph(Text("The signed determinant follows by homogeneous coordinates. "
                        + "Let H(X)=(X0,X1,s,X3-X2). Its four-dimensional derivative has determinant d/s "
                        + "and sends X to H(X). The matrix with rows A and the three coordinate derivatives "
                        + "of A has determinant one, so the matrix with rows X and the three derivatives "
                        + "of X has determinant det(M). Applying DH gives a determinant det(M)*d/s. "
                        + "Subtract delta/d times the first row from each derivative row. The last "
                        + "column becomes (d,0,0,0), while each remaining derivative row is d times "
                        + "the corresponding derivative row of F. Expansion in the last column gives "
                        + "-d^4*det(DF). Thus det(DF)=-det(M)/(s*d^3), with the sign fixed by "
                        + "row-vector action and output order (horizontal real, horizontal imaginary, height).")),
                    FormulaBlock(Eq(Call("det", Call("DF", F.Id("u"))),
                        new Formula.Fraction(F.Seq(F.Minus, Call("det", F.Id("M"))),
                            Mul(F.Id("s"), new Formula.Power(F.Id("d"), F.D(3)))))),
                    Paragraph(Text("The same frame congruence G=M*diag(1,1,1,-1)*transpose(M) gives "
                        + "det(G)=-det(M)^2 and sqrt(-det(G))=abs(det(M)). Since F2=s/d and s,d are "
                        + "positive, cancellation yields the exact weighted Jacobian below. The "
                        + "three-dimensional determinant uses the standard L2 orthonormal coordinates; "
                        + "there is no induced four-dimensional simplex measure or extra hyperplane factor.")),
                    FormulaBlock(Eq(Mul(new Formula.Power(new Formula.Subscript(F.Id("F"), F.D(2)), F.Seq(F.Minus,F.D(3))),
                            Call("abs", Call("det", Call("DF", F.Id("u"))))),
                        new Formula.Fraction(Call("sqrt", F.Seq(F.Minus,Call("det", F.Id("G")))),
                            new Formula.Power(new Formula.Binary(F.D(0),FormulaBinaryOperator.Subtract,
                                Call("q", Call("A", F.Id("u")))), F.D(2))))),
                    Paragraph(Text("Let N take the native coordinates of a point in H3 to the real triple "
                        + "(horizontal real, horizontal imaginary, height). Then F(D)=N(range(f)) "
                        + "for the same f. Packing a real triple back into (Complex,Real) is injective; "
                        + "the original injectivity of f and the inverse affine chart therefore give "
                        + "injectivity of F on D. The projection P sends the compact C onto D, so D "
                        + "is compact and measurable. The original coordinate homeomorphism makes N "
                        + "continuous, and N(range(f)) is compact and measurable in Real3. Thus the "
                        + "image correspondence and the domain conditions needed by measurable-set "
                        + "change of variables apply to the original body including its entire boundary.")),
                    Paragraph(Text("These identities give the actual change-of-variables Jacobian with the original "
                        + "frame equations. The mass application below combines measurable-set change of "
                        + "variables on the actual image with HyperbolicNormalizedDensity.raw_native_density "
                        + "and its existing exact L2 orthonormal-cube Haar calibration. Native mass equality, "
                        + "positive finite native mass and witness independence are not conclusions of the "
                        + "Jacobian calculation alone. The flat-boundary limit, face and angle identification, "
                        + "Schlaefli variation and co-volume conclusions remain separate; zero lengths are excluded.")),
                    Paragraph(Text("For this mass application, keep all six original positive lengths in the "
                        + "order (01,02,03,23,13,12) and both strict inequalities for each of the six original "
                        + "source cosines. Let M be any original frame with B(row_i(M),row_j(M))=G_ij and "
                        + "det(M)>0, and let f be any original continuous injective map from the same C into "
                        + "native H3 satisfying, at every v in C, Y=r(v) times M, B(Y,Y)=-1, Y3>0 and "
                        + "coordinates(f(v))=Psi(Y). Retain the same f, native hyperbolic metric and full "
                        + "closed cut body. In the affine chart A and domain D above, define rho_l and I_l "
                        + "by the following formulas; integralOn denotes the real set integral against "
                        + "the canonical L2 three-dimensional volume volume3.")),
                    FormulaBlock(Eq(DensityAt(F.Id("u")),
                        new Formula.Fraction(Call("sqrt", F.Seq(F.Minus, Call("det", F.Id("G")))),
                            new Formula.Power(new Formula.Binary(F.D(0), FormulaBinaryOperator.Subtract,
                                Call("q", Call("A", F.Id("u")))), F.D(2))))),
                    FormulaBlock(Eq(GramIntegral(), Call("integralOn", Density(), F.Id("D"), F.Id("volume3")))),
                    Paragraph(Text("The density is integrable and I_l is strictly positive. "
                        + "LengthGramBody.shared_radial_body gives q(A(u))<0 throughout D, including its "
                        + "boundary. The checked original Gram-frame determinant identity gives "
                        + "det(G)=-det(M)^2<0 from det(M)>0. Compactness follows from D=P(C), and the "
                        + "strictly cut barycenter has an open affine neighborhood in D, giving nonempty "
                        + "three-dimensional interior. Thus rho_l is continuous and strictly positive on "
                        + "the compact D. Compact-domain integrability and the positive volume of its "
                        + "positive support give the assertions below; no determinant-sign or "
                        + "integral-positivity conclusion is added as a hypothesis.")),
                    FormulaBlock(And(Call("IntegrableOn", Density(), F.Id("D"), F.Id("volume3")),
                        Lt(F.D(0), GramIntegral()))),
                    Paragraph(Text("Use the existing HyperbolicNormalizedDensity normalization convention. "
                        + "In Amb=WithLp 2 (Complex times Real), Q is the parallelepiped of the standard "
                        + "real orthonormal basis, and c3 is its raw ambient Hausdorff three-mass. "
                        + "The product orthonormal basis proves real dimension three. Haar uniqueness "
                        + "and the unit canonical volume of an orthonormal parallelepiped identify "
                        + "ambient Hausdorff measure with c3 times ambient volume. The compact Q has "
                        + "nonempty interior, so c3 is strictly positive and finite; these facts are derived.")),
                    FormulaBlock(Eq(F.Id("Amb"), Call("WithLp", F.D(2), Call("Product", F.Id("Complex"), F.Id("Real"))))),
                    FormulaBlock(Eq(F.Id("Q"), Call("parallelepiped", Call("toBasis",
                        Call("stdOrthonormalBasis", F.Id("Real"), F.Id("Amb")))))),
                    FormulaBlock(Eq(F.Id("c3"), Call("mass", Call("hausdorffMeasure", F.D(3), F.Id("Amb")), F.Id("Q")))),
                    FormulaBlock(And(Lt(F.D(0), F.Id("c3")), Lt(F.Id("c3"), F.Infty),
                        Eq(Call("hausdorffMeasure", F.D(3), F.Id("Amb")),
                            Call("smul", F.Id("c3"), Call("volume", F.Id("Amb")))))),
                    Paragraph(Text("The literal packing z maps to WithLp.toLp 2 (Complex.mk(z0,z1),z2). "
                        + "It is exactly the real linear isometry obtained from the product orthonormal "
                        + "basis in that coordinate order, preserving canonical volume and Hausdorff "
                        + "measure. On the positive-height coordinate subtype its inverse unpack has "
                        + "unpack(x)2=height(x), and unpack(coordinatesEquiv(p))=N(p). Applying the "
                        + "existing raw_native_density to the same set range(f), then transporting its "
                        + "withDensity lower integral through this measurable isometric unpack, gives "
                        + "the raw mass formula below. The restriction to range(unpack) disappears on "
                        + "the actual image contained in that range. Here weight(z)=ofReal(z2^(-3)), "
                        + "lowerIntegral denotes the extended nonnegative set integral, and rawNativeMeasure "
                        + "is Hausdorff three-measure for the original native H3 metric.")),
                    FormulaBlock(Eq(NativeMass("rawNativeMeasure"), Mul(F.Id("c3"),
                        Call("lowerIntegral", F.Id("weight"), Call("image", F.Id("F"), F.Id("D")), F.Id("volume3"))))),
                    Paragraph(Text("The sets D and F(D)=N(range(f)) are Borel because they are compact; "
                        + "range(f) itself is compact and Borel by continuity of the same original f. "
                        + "The previously checked literal map F is injective on D, has its ambient "
                        + "derivative at every point of D, and satisfies F2(u)^(-3)*abs(det(DF(u)))=rho_l(u). "
                        + "Its within-derivative therefore instantiates measurable-set change of variables "
                        + "on the full closed D, with no cut-equality or inactive-boundary point removed. "
                        + "Define ofRealDensity(u)=ofReal(rho_l(u)) and lowerGramIntegral_l as its lower "
                        + "integral over D. The weighted Jacobian equates the image lower integral with "
                        + "lowerGramIntegral_l; real integrability and nonnegativity identify it with ofReal(I_l).")),
                    FormulaBlock(Eq(LowerGramIntegral(),
                        Call("lowerIntegral", F.Id("ofRealDensity"), F.Id("D"), F.Id("volume3")))),
                    FormulaBlock(Eq(Call("lowerIntegral", F.Id("weight"),
                        Call("image", F.Id("F"), F.Id("D")), F.Id("volume3")), LowerGramIntegral())),
                    FormulaBlock(Eq(LowerGramIntegral(), Call("ofReal", GramIntegral()))),
                    Paragraph(Text("Set muNorm=c3 inverse smul rawNativeMeasure, exactly as in the existing "
                        + "normalization. Cancellation of the nonzero finite c3 yields the exact "
                        + "same-witness mass identities below. The toReal identity uses I_l>0. "
                        + "Consequently both normalized and raw native masses are strictly positive "
                        + "and finite.")),
                    FormulaBlock(Eq(F.Id("muNorm"), Call("smul", Call("inv", F.Id("c3")), F.Id("rawNativeMeasure")))),
                    FormulaBlock(new Formula.RelationChain(FormulaRelationOperator.Equal,
                        [NativeMass("muNorm"), LowerGramIntegral(), Call("ofReal", GramIntegral())])),
                    FormulaBlock(Eq(Call("toReal", NativeMass("muNorm")), GramIntegral())),
                    FormulaBlock(Eq(NativeMass("rawNativeMeasure"), Mul(F.Id("c3"), Call("ofReal", GramIntegral())))),
                    FormulaBlock(And(Lt(F.D(0), NativeMass("muNorm")), Lt(NativeMass("muNorm"), F.Infty),
                        Lt(F.D(0), NativeMass("rawNativeMeasure")), Lt(NativeMass("rawNativeMeasure"), F.Infty))),
                    Paragraph(Text("For any two admissible original witness pairs (M,f) and (Mprime,fprime) "
                        + "with the same length vector l, the normalized masses agree because each equals "
                        + "ofReal(I_l); the raw masses agree because each equals c3*ofReal(I_l). "
                        + "The conclusion is equality of masses and asserts no equality of the two ranges. "
                        + "This application uses the original literal Jacobian and image identities, "
                        + "raw_native_density, Hausdorff-Haar calibration, measurable-set change of "
                        + "variables and real/lower-integral conversion. It closes the native mass "
                        + "application, while flat-boundary limits, actual face and angle identification, "
                        + "Schlaefli variation, co-volume and full CFMP completion remain separate."))),
                DescribeRole.Theorem),
            Paragraph(Text("Application: the eight original face planes and the twelve truncation incidences. Keep the same arbitrary original l, M and f as in the mass application: all six lengths are positive, all six source cosines are strictly between -1 and 1, B(row_i(M),row_j(M))=G_ij, det(M)>0, and f:C(l)->H3 is continuous and injective with lift(f(v))=r(v) times M future unit timelike. No halfspace-image, face-germ or angle conclusion is assumed. The source cosine in slot q is the cosine of "),
                Ref("D5/S3/Geometry/Hyperideal/FourCycleEnvelopes.cosine"),
                Text(" evaluated on the six cosh lengths in the order frame(q,0),...,frame(q,5) of "),
                Ref("D5/S3/Geometry/Hyperideal/FourCycleCurvature.frame"),
                Text(". For q=0,...,5 these argument-slot rows are (0,1,2,3,4,5), (1,2,0,4,5,3), (2,1,0,5,4,3), (3,1,5,0,4,2), (4,5,0,1,2,3), (5,4,0,2,1,3). All distances below use the original native H3 metric.")),
            Paragraph(Text("Write a_i(v)=(Gv)_i for the original cap row, J=diag(1,1,1,-1), c_i=row_i(M), and n_i(a)=-J_aa*(inverse(M))_ai for the outward side normal. Thus B(c_j,n_i)=-delta_ji. For v in the full original C(l), put s(v)=sqrt(-q(v))>0. The original coordinate contract gives B(lift(f(v)),n_i)=-v_i/s(v) and B(lift(f(v)),c_i)=a_i(v)/s(v). These are the same coordinate-zero side and cap-row-zero faces, with their original outward signs.")),
            Paragraph(Text("The eight nonpositive native supports recover range(f) exactly. Indeed, for any native p satisfying B(lift(p),n_i)<=0 and B(lift(p),c_i)<=0 for every i, set b=lift(p) times inverse(M) and S=sum_i b_i. The side inequalities say b_i>=0. Frame inversion and the unit lift give q(b)=-1, excluding b=0; hence S>0. Then v=b/S has nonnegative coordinates with sum one, a_i(v)<=0 and q(v)=-1/S^2. Its positive radial normalization is b, so lift(f(v))=lift(p), and lift injectivity gives f(v)=p. Conversely the two displayed support evaluations give all eight inequalities on range(f). This uses the negativity and radial normalization from "),
                Ref("D5/S3/Geometry/Hyperideal/LengthGramBody.shared_radial_body"),
                Text(" and the native lift identities from "),
                Ref("D5/S3/Geometry/Hyperideal/LengthGramMetricSegments"),
                Text("; it constructs a preimage in the original full C(l).")),
            Paragraph(Text("Each cap normal has B(c_i,c_i)=1. Each n_k is nonzero by frame duality. Choose an original edge midpoint with its two endpoint labels different from k; the endpoint supports in "),
                Ref("D5/S3/Geometry/Hyperideal/LengthGramPolytope.cut_body_polytope"),
                Text(" put its original lift on B(Y,n_k)=0. Spatial Cauchy-Schwarz for the future unit timelike Y makes B(n_k,n_k)>0. Apply "),
                Ref("D5/S3/Geometry/HyperbolicPlaneRealization.supporting_plane_isometry"),
                Text(" to these eight spacelike normals. For every i there are actual isometries eSide_i,eCap_i from the full native H2 upper half-plane into H3 with ranges exactly {p:B(lift(p),n_i)=0} and {p:B(lift(p),c_i)=0}, respectively. Positivity of s(v) proves the exact same-f traces f({v in C(l):v_i=0})=range(f) intersect range(eSide_i) and f({v in C(l):a_i(v)=0})=range(f) intersect range(eCap_i). The full planes and the bounded original face traces are distinguished.")),
            Paragraph(Text("The eight original outward normals also have explicit native coordinate vectors. Keep the same six positive lengths, nonsingular frame M and original radial realization f. For each support take R=n_i on a coordinate-zero side and R=c_i on a cap, and put N=R/sqrt(B(R,R)). The preceding spacelikeness makes this normalization positive, and B(N,N)=1. The support evaluation is B(lift(f(v)),N)=readout(v)/(s(v)*sqrt(B(R,R))), where readout(v) is -v_i for a side and a_i(v) for a cap. It is nonpositive on the entire original C(l), with its original outward sign.")),
            Paragraph(Text("At every point of the full closed zero-support face, write p=(x,y,h) for the coordinates of the same f(v), so h>0. For N=(N0,N1,N2,N3), define a=(h*(N0+x*(N2-N3)),h*(N1+y*(N2-N3)),h^2*(N2-N3)). The differential of the native Lorentz lift at p sends a exactly to N. Consequently a dot a/h^2=1, and t dot a/h^2=0 for every native coordinate tangent t whose lift differential is B-orthogonal to N. Thus a is the outward unit normal for this particular supporting face, including at its edges and vertices; incident supports retain their separate normals.")),
            Paragraph(Text("For the normalized defining function F_N(p)=B(lift(p),N), the coordinate line p+u*a satisfies d/du F_N(p+u*a) at u=0 equal to 1. For every sufficiently small positive u its height remains positive and F_N(p+u*a)>0, so it leaves the original nonpositive support halfspace. This is a local outward crossing and unit normalization at u=0. The construction does not require the coordinate line to be a global geodesic or to have constant speed, and supplies no moving-boundary flux identity.")),
            Paragraph(Text("The truncation incidences are precisely the twelve ordered choices (i,k) with i!=k: cap 0 with sides 1,2,3; cap 1 with sides 0,2,3; cap 2 with sides 0,1,3; cap 3 with sides 0,1,2. For any such pair choose the remaining distinct labels j,h, and let E(i,j) denote the original endpoint of cut_body_polytope. Convexity and those endpoint supports put x=(E(i,j)+E(i,h))/2 in the same C(l). At x exactly a_i(x)=0 and x_k=0 are active; every other cap row is strictly negative and every other coordinate is strictly positive. There is no cap-i/side-i incidence in this claim.")),
            Paragraph(Text("Let Y=lift(f(x)), n=n_k, r=sqrt(B(n,n))>0, U=-n/r and V=-c_i. Exact duality at i!=k gives B(U,U)=B(V,V)=1, B(Y,U)=B(Y,V)=0 and B(U,V)=0. Apply "),
                Ref("D5/S3/Geometry/Hyperideal/ActualRaysJointAngle.actual_rays_joint_angle"),
                Text(" to these literal Y,U,V. It supplies isometries gc,gs:R->H3 through the same f(x), with lift(gc(t))=cosh(t)Y+sinh(t)U and lift(gs(t))=cosh(t)Y+sinh(t)V for every real t. The cap ray gc stays on cap i; the side ray gs stays on side k. Since B(U,n)<0 and B(V,c_i)=-1, positive time crosses strictly inward through side k on gc and through cap i on gs.")),
            Paragraph(Text("The six strict inactive supports at x persist by continuity for both rays on one common interval [0,epsilon), with epsilon>0. The eight-support reconstruction puts both rays in range(f) on that interval. Compactness of C(l), continuity and injectivity of this same f give a continuous inverse on its image. Thus there are continuous vc,vs:[0,epsilon)->C(l) with f(vc(t))=gc(t), f(vs(t))=gs(t), a_i(vc(t))=0 and vs(t)_k=0. For 0<t<epsilon, vc(t)_k>0 and a_i(vs(t))<0; for every a!=k both vc(t)_a and vs(t)_a are positive, and for every a!=i both a_a(vc(t)) and a_a(vs(t)) are negative. These are actual original preimages with all active and inactive supports. The exact trace identities place the local gc in range(eCap_i) and the local gs in range(eSide_k). Global metric lines are supplied, while body containment is asserted only on this local interval.")),
            Paragraph(Text("The normal section is tied to the original truncation ridge. Take z=E(i,j), Z=lift(f(z)), and D=dist(f(x),f(z)). The remaining h-coordinate is positive at x and zero at z, so original injectivity gives D>0. Define T=(Z-cosh(D)Y)/sinh(D). The existing lift identity B(Y,Z)=-cosh(D), unit lifts and cosh(D)^2-sinh(D)^2=1 give B(T,T)=1 and B(Y,T)=0. Both endpoints have the active ridge supports, so B(T,n_k)=B(T,c_i)=0. Consequently B(T,U)=B(T,V)=0.")),
            Paragraph(Text("Applying supporting_plane_isometry to T gives an isometry eNormal:H2->H3 whose full range is {p:B(lift(p),T)=0}; it contains both global face lines gc and gs. Applying actual_rays_joint_angle to the ridge direction T gives an isometry gr:R->H3 with gr(0)=f(x), lift(gr(t))=cosh(t)Y+sinh(t)T and gr(D)=f(z). For each t in [0,D], the isometry equations give dist(f(x),gr(t))+dist(gr(t),f(z))=D. Apply "),
                Ref("D5/S3/Geometry/Hyperideal/LengthGramMetricSegments.same_body_metric_segments"),
                Text(" to the original x,z: its full ambient-between characterization places gr(t) in the f-image of the original affine segment [x,z] in C(l). Thus the section is perpendicular to an actual endpoint-reaching original ridge with original segment preimages.")),
            Paragraph(Text("For s,t>0 let K(s,t)=(s^2+t^2-dist(gc(s),gs(t))^2)/(2*s*t). The joint-angle conclusion of actual_rays_joint_angle applied above gives arccos(K(s,t))->arccos(B(U,V))=pi/2 as (s,t)->(0,0) within (0,infinity) times (0,infinity). This is the unrestricted two-positive-parameter limit in the native metric, with no constraint on s/t. Combined with the common positive interval, inward crossings, exact same-f face traces and original-ridge normal section, it identifies the right-angle germ at every one of the twelve truncation incidences.")),
            Paragraph(Text("Application: the six original side/side angle germs. Retain all six positive lengths, all six strict source cosines, and the same original M,f and full C(l). For edge slots 01,02,03,23,13,12 the active side pairs (k,h) are (2,3),(1,3),(1,2),(0,1),(0,2),(0,3). Normalize the outward normals as A=n_k/sqrt(B(n_k,n_k)) and Bnormal=n_h/sqrt(B(n_h,n_h)). Frame inversion gives B(n_i,n_j)=(inverse(G))_ij. Cofactor expansion in each original frame(q) order gives the two diagonal cofactors as minus the corresponding positive source radicands and the mixed cofactor as the source numerator. Since det(G)<0, both normal squares are positive; division by their positive square roots gives B(A,Bnormal)=-phi_q(l), with the original signed source cosine and no replacement of the slot order.")),
            Paragraph(Text("Let c=B(A,Bnormal) and sigma=sqrt(1-c^2). The strict source cosine bounds give sigma>0. At x=(E(i,j)+E(j,i))/2 in the original C(l), the active coordinates x_k,x_h vanish, the other two coordinates are positive, and all four cap rows are strictly negative. Put Y=lift(f(x)) and use the inward unit directions U=(c*A-Bnormal)/sigma and V=(c*Bnormal-A)/sigma. Their exact identities are B(U,U)=B(V,V)=1, B(Y,U)=B(Y,V)=0, B(U,A)=B(V,Bnormal)=0, B(U,Bnormal)=B(V,A)=-sigma and B(U,V)=-c=phi_q(l). Thus U follows side k inward through side h, and V follows side h inward through side k.")),
            Paragraph(Text("Apply "),
                Ref("D5/S3/Geometry/Hyperideal/ActualRaysJointAngle.actual_rays_joint_angle"),
                Text(" to this literal Y,U,V. It gives global isometries gu,gv:R->H3 through f(x), with lifts cosh(t)Y+sinh(t)U and cosh(t)Y+sinh(t)V. Continuity preserves the two inactive side inequalities and all four strict cap inequalities on one common interval [0,epsilon), epsilon>0. The eight-support reconstruction and continuous inverse of this same f give continuous vu,vv:[0,epsilon)->C(l) with f(vu(t))=gu(t), f(vv(t))=gv(t), vu(t)_k=0 and vv(t)_h=0. At positive t the other active coordinates are strictly positive; both inactive coordinates remain strictly positive and every cap row remains strictly negative. The local rays therefore lie on the original bounded face traces. Body containment is restricted to that interval.")),
            Paragraph(Text("Tie the section to the ordered original endpoint z=E(i,j). Set Z=lift(f(z)), D=dist(f(x),f(z)) and T=(Z-cosh(D)Y)/sinh(D). The cap row at i is strictly negative at x and zero at z, so x!=z and D>0 by the original injectivity. The unit-lift and distance identities give B(T,T)=1 and B(Y,T)=0. Both original endpoints lie on sides k,h, hence B(T,n_k)=B(T,n_h)=0 and consequently B(T,U)=B(T,V)=0. The existing supporting_plane_isometry gives an actual isometry eNormal:H2->H3 with full range {p:B(lift(p),T)=0}, containing both global face lines gu,gv.")),
            Paragraph(Text("The same ray supplier gives a global isometric ridge line gr with gr(0)=f(x), gr(D)=f(z), lift(gr(t))=cosh(t)Y+sinh(t)T and both original side supports zero for all real t. Apply "),
                Ref("D5/S3/Geometry/Hyperideal/LengthGramMetricSegments.same_body_metric_segments"),
                Text(" to x,z. Its full ambient-between characterization and the continuous original-range inverse yield a continuous w:[0,D]->C(l), with f(w(t))=gr(t), w(t) in the original affine segment [x,z], w(0)=x and w(D)=z. This supplies a section perpendicular to an actual original ridge direction and original segment preimages, from the coefficient midpoint to the ordered endpoint.")),
            Paragraph(Text("For s,t>0 let K(s,t)=(s^2+t^2-dist(gu(s),gv(t))^2)/(2*s*t). The supplier's full joint-angle limit gives arccos(K(s,t))->arccos(phi_q(l)) as (s,t)->(0,0) within the full positive quadrant, without restricting s/t. These six midpoint angle germs use one common original body and one common M,f; their existence follows by selecting shared_radial_body once using the q=0 strict cosine, then applying the construction to each q. Together with the original face traces, inward preimages and ridge-normal section, this realizes all six prescribed source angles at their specified midpoints.")),
            Paragraph(Text("Application: the prescribed six original endpoint distances. For any original witnesses M and f with the displayed Gram and radial-coordinate equations, let i,j be the original endpoints of slot q, C=cosh(l_q)>1 and r=(C-1)/(C+1)>0. The original polytope supplier puts both ordered endpoint vectors E(i,j),E(j,i) in this same C(l). Their unnormalized Lorentz vectors are X=(C*M_i+M_j)/(C+1) and Z=(M_i+C*M_j)/(C+1). The exact diagonal and mixed Gram entries give B(X,X)=B(Z,Z)=-r and B(X,Z)=-C*r. The original radial map therefore normalizes both by the same positive sqrt(r), yielding B(lift(f(E(i,j))),lift(f(E(j,i))))=-C. The existing lift_cosh identity gives cosh of the actual native endpoint distance equal to cosh(l_q). Both arguments are nonnegative, so the pinned Mathlib cosh_injOn theorem gives dist(f(E(i,j)),f(E(j,i)))=l_q. This holds for every original q and every such same-body M,f; selecting shared_radial_body once supplies them simultaneously under the original six-positive-length and six-strict-cosine assumptions.")),
            Paragraph(Text("Application: the full six original ridge intervals. For slot q with ordered endpoints i,j and complementary side indices k,h, the original trace Rq={v in C(l):v_k=v_h=0} equals the entire affine segment [E(i,j),E(j,i)]. Indeed all remaining coordinates except v_i,v_j vanish, v_i+v_j=1, and the two cap inequalities reduce to v_i-C*v_j<=0 and v_j-C*v_i<=0 with C=cosh(l_q)>1. Therefore a=((C+1)*v_i-1)/(C-1) belongs to [0,1] and v=a*E(i,j)+(1-a)*E(j,i). Conversely convexity of the original C(l) and the endpoint side equalities place every such combination in Rq.")),
            Paragraph(Text("The prescribed endpoint distance is l_q. Apply same_body_metric_segments to these two literal ordered endpoints and the same original f: it supplies an isometry gamma:[0,l_q]->H3 with gamma(0)=f(E(i,j)) and gamma(l_q)=f(E(j,i)). Its complete range is f(Rq), and it also equals {p:dist(f(E(i,j)),p)+dist(p,f(E(j,i)))=l_q}, the full ambient metric-between set. The continuous inverse of the same compact injective body map gives w:[0,l_q]->C(l), with f(w(t))=gamma(t), the ordered endpoint values, and range(w)=Rq. Selecting shared_radial_body once under the original six-positive-length and six-strict-cosine assumptions supplies one common M,f for all six full intervals. The original geometric side traces are identified by the preceding eight-support reconstruction, so their simultaneous vanishing uses this same body and these same labels.")),
            Paragraph(Text("Application: the prescribed angle at every point of each original closed ridge, including both truncation endpoints. Fix the same original M,f and a slot q. At any x in Rq, the original side-plane trace identity places f(x) on the same two supporting planes. Their signed normalized normals give two inward unit directions U,V, with B(U,V)=phi_q(l), independently of x. The actual_rays_joint_angle supplier gives actual unit-speed geodesics gu,gv based at f(x). Their native comparison-angle limit on the full positive parameter quadrant is arccos(phi_q(l)); no parameter-ratio restriction is introduced.")),
            Paragraph(Text("These rays have pointwise local preimages in the same original C(l): each remains on its corresponding side trace, enters the other side strictly at positive parameter, and retains all cap inequalities as nonpositive. At a truncation endpoint an active cap is allowed to remain zero. The two edge-frame cap supports are multiplied by cosh(t), because both inward directions are Lorentz-orthogonal to those frame rows. The other cap supports and the remaining side coordinates are strict on the whole original ridge; continuity preserves them near the given point. Eight-support reconstruction places the two local rays in the same original body image, and its continuous inverse gives the local preimages. The positive local interval may depend on q and x.")),
            Paragraph(Text("Choose an original ordered endpoint z different from x; the two ordered endpoints are distinct by the original polytope supplier, so this choice adds no source assumption. With D=dist(f(x),f(z))>0, the actual ridge direction is T=(lift(f(z))-cosh(D)*lift(f(x)))/sinh(D). It is unit spacelike, orthogonal to lift(f(x)), U and V. Apply supporting_plane_isometry to obtain the complete isometric H2 section {p:B(lift(p),T)=0}; both face rays lie in this section. The actual ridge geodesic reaches f(z) at parameter D and has continuous original segment preimages. One shared_radial_body selection under the original six-positive-length and six-strict-cosine assumptions supplies the same M,f for every q and every point of Rq. These are pointwise witnesses; no uniform local interval or continuously selected witness family is asserted.")),
            Paragraph(Text("Application: label permutation naturality. A permutation sigma sends each new vertex label i to the old label sigma(i). Keep the original six-slot order 01,02,03,23,13,12. For a new slot q with endpoints i,j, let pi_sigma(q) be the old unordered slot with endpoints sigma(i),sigma(j), and put l_sigma(q)=l(pi_sigma(q)). The coordinate pullback P_sigma(v)_i=v_sigma(i) gives G(l_sigma)=G(l).submatrix(sigma,sigma), q_lsigma(P_sigma(v))=q_l(v), and r_lsigma(P_sigma(v))=P_sigma(r_l(v)). The simplex and four cap-row inequalities give a continuous body equivalence P_sigma:C(l)->C(l_sigma), with continuous inverse. Coordinate and length pullbacks compose as P_sigma(P_tau(v))=P_(tau*sigma)(v) and (l_tau)_sigma=l_(tau*sigma), a right action under this convention.")),
            Paragraph(Text("Keep all six original positive lengths and all six strict original source cosines. Select the original M,f once with shared_radial_body. For every sigma define N_i=M_sigma(i) and g_sigma=f composed with P_sigma inverse. Reindexing the finite sums gives B(N_i,N_j)=G(l_sigma)_ij and r_lsigma(P_sigma(v)) times N=r_l(v) times M. Consequently g_sigma satisfies the exact original future-unit radial-coordinate contract for l_sigma, is continuous and injective, and g_sigma(P_sigma(v))=f(v). Its actual H3 image is exactly range(f), simultaneously for every sigma. The identity isometry of the full ambient H3 restricts to an isometry between these two body images.")),
            Paragraph(Text("All four side coordinates and four cap-row evaluations retain their original signs: the new side-i coordinate of P_sigma(v) is v_sigma(i), and the new cap-i row evaluation equals the old cap-sigma(i) row evaluation. For each of the twelve ordered pairs i!=j, P_sigma(E_l(sigma(i),sigma(j)))=E_lsigma(i,j). This preserves ordered endpoints, rather than merely their unordered edge. The transported row determinant is det(N)=sign(sigma)*det(M); odd permutations therefore do not preserve the positive-determinant convention of the originally chosen M. This construction transports one realization and does not claim a separately chosen positive-determinant target realization or rederived strict-cosine bounds for l_sigma.")),
            Paragraph(Text("For any two already given injective exact realizations f:C(l)->H3 and g:C(l_sigma)->H3 with their Gram and future-unit radial-coordinate contracts, the same reindexing gives equality of every corresponding native H3 distance. The existing lift_cosh identity and cosh_strictMonoOn on nonnegative distances supply a body-image isometry sending f(v) to g(P_sigma(v)). This statement does not extend arbitrary independently chosen frames to an isometry of the full ambient H3. Label naturality compares the relabeled length models; arbitrary permutations are not asserted to act as vertex-permuting metric automorphisms of a fixed asymmetric length model.")),
            Paragraph(Text("Application: positive frame orientation for every vertex relabeling. Keep the same source entrance with all six positive lengths and all six strict source cosines, and select the original M/f once. Put Q=diag(1,-1,1,1). Native upper-half-space conjugation C(z,h)=(conj(z),h) is an involutive ambient isometry, and lift(C(p))=lift(p) times Q. The pinned complex conjugation distance identity and the existing product-distance formula preserve hyperbolicDist directly. The diagonal Q preserves every Lorentz pairing and leaves the time coordinate unchanged, while det(Q)=-1.")),
            Paragraph(Text("For an even sigma take N=M.submatrix(sigma,id), E=id and g=f composed with inverse(P_sigma). For an odd sigma take N=(M.submatrix(sigma,id)) times Q, E=C and g=C composed with f composed with inverse(P_sigma). In both cases the exact relabeled Gram matrix and the original future-unit radial-coordinate contract hold, det(N)=det(M)>0, and E(f(v))=g(P_sigma(v)). Thus a positive-determinant target realization is explicitly constructed for each sigma, with continuity and injectivity inherited from the same original realization. The full images satisfy E(range(f))=range(g); the odd case transports the original image by conjugation, without asserting that the two images are equal as subsets.")),
            Paragraph(Text("For each i!=j, E maps the original ordered endpoint near sigma(i) on the edge sigma(i),sigma(j) to the target ordered endpoint near i on the edge i,j. All four side coordinates and all four cap-row readouts retain the same scalar values under P_sigma. Consequently E maps each complete original side-sigma(i) zero trace to the target side-i zero trace, and each complete original cap-sigma(i) zero trace to the target cap-i zero trace. These are the original cut-body face traces; the application supplies no further supporting-plane normal identities. It requires no separately chosen target realization and proves no relabeled strict-cosine formula or vertex-permuting automorphism of a fixed asymmetric model.")),
            Paragraph(Text("Application: the exact hulls and pairwise intersections of the eight original supporting traces. For all six independently positive lengths, define cap_i={v in C(l):(Gv)_i=0} and side_k={v in C(l):v_k=0}. Retain the literal ordered endpoints E(i,j) from "),
                Ref("D5/S3/Geometry/Hyperideal/LengthGramPolytope.cut_body_polytope"),
                Text(". Each trace is compact and convex. The corresponding linear functional is nonpositive on C(l), so a strict interior point of an original segment can lie on its zero trace only if both endpoints lie on that trace. Thus the traces are extreme subsets of this same C(l).")),
            Paragraph(Text("The pinned Mathlib IsExtreme.extremePoints_eq theorem identifies the extreme points of each trace with its intersection with the twelve original extreme points. Compact convex Krein-Milman, together with closedness of the convex hull of a finite set, then gives each whole trace as the convex hull of its selected original endpoints. The endpoint support equations select exactly E(i,j) with j!=i for cap_i, and exactly E(i,j) with i!=j and i,j!=k for side_k. Consequently cap_i=convexHull{E(i,j):j!=i} and side_k=convexHull{E(i,j):i!=j,i,j!=k}. Original endpoint injectivity makes these endpoint sets have exactly three and six elements, respectively.")),
            Paragraph(Text("Apply the same extreme-subset argument to intersections of traces. Distinct cap traces are disjoint, and cap_i is disjoint from side_i. If i!=k and j,h are the two remaining distinct labels, cap_i intersect side_k is the entire original affine segment [E(i,j),E(i,h)]. If k,h are distinct and i,j are the complementary labels, side_k intersect side_h is the entire original affine segment [E(i,j),E(j,i)]. These equations describe the full closed intersections, with the endpoints in the same original C(l); they assert more than midpoint incidence.")),
            Paragraph(Text("For the actual native H3 interpretation, retain the same original M,f supplied by one shared_radial_body selection under all six positive lengths and all six strict source cosines. The preceding exact supporting-plane trace identities identify f(cap_i) and f(side_k) with range(f) intersect their respective native supporting planes. Injectivity of this same f preserves all the displayed intersections and disjointness statements. Apply "),
                Ref("D5/S3/Geometry/Hyperideal/LengthGramMetricSegments.same_body_metric_segments"),
                Text(" to the literal endpoints of each nonempty intersection. Its image is the full ambient metric-between set, and it has an isometric arclength parametrization with the displayed ordered endpoints. More generally, the coefficient convexity of every cap and side trace and the same-body segment theorem imply that the full native metric-between set of any two points on that trace stays on that trace. This is geodesic convexity in the native metric; no Euclidean convex hull of upper-half-space coordinates is used.")),
            Paragraph(Text("Application: the affine dimension of all eight coefficient faces. This coefficient statement still requires only the six independently positive lengths. For cap_i, index its three original endpoints by j!=i. In a linear relation among E(i,j), reading coordinate j isolates that endpoint's strictly positive j-coordinate. Thus all coefficients vanish: the three endpoints are linearly independent, hence affinely independent. Their exact cap hull and the pinned Mathlib affine-span and affine-independent finrank formulas give dimension two for the direction of the affine span of the entire cap_i.")),
            Paragraph(Text("For side_k choose the complementary distinct labels i,j,h. The three points E(i,j),E(i,h),E(j,h) are in the same original side_k. In a linear relation, apply the original cap-i row: the first two readouts vanish while the third is strictly negative, so the third coefficient vanishes. Coordinates j and h then isolate the first two positive endpoint coordinates, forcing their coefficients to vanish as well. This gives an affine-independent triple and a dimension-two lower bound for the whole side. Conversely each side point x has x_k=0 and x_i+x_j+x_h=1 with nonnegative coefficients; it lies in the convex hull of the three standard coordinate vectors e_i,e_j,e_h. The affine span of this enclosing coordinate triangle has dimension at most two. Monotonicity of direction finrank yields the matching upper bound, so every original side_k has affine dimension two.")),
            Paragraph(Text("Together with the preceding exact hull application, each coefficient cap is the convex hull of three affinely independent original endpoints, and each coefficient side is a two-dimensional convex hull of six original extreme endpoints. These are statements about the coefficient faces' affine spans. They do not by themselves prove nonempty interior in the actual native H2 face planes, their complete cyclic boundaries, or a topological polygon statement in H3.")),
            Paragraph(Text("Application: the complete intrinsic boundaries of the original coefficient faces. Keep six independently positive lengths, the same C(l), cap_i, side_k and the literal ordered endpoints E(i,j). Intrinsic frontier means frontier in the affine span of the coefficient face, included back into coefficient space; it is not the ambient frontier in Real4 or a frontier in a native H2 plane. The preceding dimension and hull applications identify two-dimensional coefficient faces with three and six distinct original extreme endpoints.")),
            Paragraph(Text("The boundary derivation uses finite continuous linear inequalities on each face's affine span. Its defining affine equations, sum(x)=1 together with x_k=0 for side_k or (Gx)_i=0 for cap_i, hold throughout that affine span. The remaining coordinate and cap-row inequalities therefore describe exactly the original face there. A point where every remaining inequality is strict has an open neighborhood contained in the face, by continuity and finite intersection. If a supporting functional vanishes at x and is strictly negative at some original endpoint y on the face, an intrinsic-interior neighborhood would contain x+t*(x-y) for some t>0; the functional is positive there, a contradiction. These reusable open-neighborhood and intrinsic-extension facts identify the intrinsic frontier exactly with the union of the zero traces of the remaining inequalities. Strict witnesses are selected from the original endpoint support equations separately for each inequality; no extra length relation or simultaneous strict-witness premise is imposed.")),
            Paragraph(Text("For cap_i the other cap zero traces are empty, and its own side zero trace is empty. Its entire intrinsic frontier is thus the union of cap_i intersect side_r over r!=i. For side_k the cap_k zero trace is empty. Its entire intrinsic frontier is the union of side_k intersect side_r and cap_r intersect side_k over r!=k. Each nonempty trace is the complete original supporting segment from the preceding intersection application, including its two endpoints.")),
            Paragraph(Text("Choose distinct a,b,c complementary to i. The cap's ordered cycle T is displayed below, and its three closed edges are [T_q,T_(q+1)] with q in Fin3 and cyclic addition. In order these edges are cap_i intersect side_c, cap_i intersect side_a and cap_i intersect side_b. Their union exhausts the intrinsic frontier of cap_i.")),
            FormulaBlock(Eq(Call("T"), Call("tuple",
                Call("E", F.Id("i"), F.Id("a")),
                Call("E", F.Id("i"), F.Id("b")),
                Call("E", F.Id("i"), F.Id("c"))))),
            Paragraph(Text("Choose distinct i,j,h complementary to k. The side's ordered cycle H is displayed below, and its six closed edges are [H_q,H_(q+1)] with q in Fin6 and cyclic addition. Their supports in order are side_k intersect side_h, side_k intersect cap_j, side_k intersect side_i, side_k intersect cap_h, side_k intersect side_j and side_k intersect cap_i. Thus original ridge segments and truncation segments alternate, and their union exhausts the intrinsic frontier of side_k.")),
            FormulaBlock(Eq(Call("H"), Call("tuple",
                Call("E", F.Id("i"), F.Id("j")),
                Call("E", F.Id("j"), F.Id("i")),
                Call("E", F.Id("j"), F.Id("h")),
                Call("E", F.Id("h"), F.Id("j")),
                Call("E", F.Id("h"), F.Id("i")),
                Call("E", F.Id("i"), F.Id("h"))))),
            Paragraph(Text("Original endpoint injectivity makes T and H injective, so the cycles contain exactly three and six distinct vertices and every displayed edge has distinct endpoints. The cap intersections side_c with side_a, side_a with side_b and side_b with side_c, all inside cap_i, are the singletons {E(i,b)}, {E(i,c)} and {E(i,a)}, respectively. These are all pairs of distinct cap edges. For the six side edges, every edge q intersects its next edge only in {H_(q+1)}, including the last-first pair. Every other pair of distinct side edges is disjoint: explicitly, if q!=r, q+1!=r and r+1!=q in Fin6, their intersection is empty. The nonadjacent table consists of the nine unordered pairs (0,2), (0,3), (0,4), (1,3), (1,4), (1,5), (2,4), (2,5) and (3,5). The original support labels reduce these intersections to distinct-cap disjointness, cap_i intersect side_i being empty, or three distinct side traces having empty intersection.")),
            Paragraph(Text("For a given original injective radial-coordinate realization f with its frame M, injectivity transports the displayed segment images, singleton intersections and disjointness to this same native image. The same_body_metric_segments supplier identifies each complete segment image with its full ambient native metric-between set and gives an isometric arclength parametrization. If a common f is selected through shared_radial_body, retain all six positive lengths and all six strict original source cosines and use that one selection for every face. These statements concern images under the supplied same f; they do not identify its image of a coefficient intrinsic frontier with a native intrinsic frontier, construct a homeomorphism onto a native supporting-plane region, or establish native face-plane interior. The exact named cap and side support tables classify the displayed original traces and their edges; they do not assert a classification of every arbitrary face of the body.")),
            Paragraph(Text("Application: the original face regions in their full native H2 planes. Retain all six positive lengths and all six strict source cosines, and select shared_radial_body once. The resulting Gram frame M and continuous injective radial-coordinate map f:C(l)->H3 are the same for every face below. Index the eight faces by the four original sides and four original caps. For a side j use F_j=side_k, L_j(v)=-v_k and N_j=n_k; for a cap j use F_j=cap_i, L_j(v)=(Gv)_i and N_j=c_i. The earlier spacelike-normal result and "),
                Ref("D5/S3/Geometry/HyperbolicPlaneRealization.supporting_plane_isometry"),
                Text(" give an isometry e_j:H2->H3 whose full range is {p:B(lift(p),N_j)=0}. Define the native face region R_j={z in H2:e_j(z) in f(F_j)}. Interior and frontier of R_j use the actual topology of the full native H2 upper half-plane. The coefficient intrinsic interior and frontier continue to use the affine span of F_j.")),
            Paragraph(Text("Write s(v)=sqrt(-q(v))>0. For all eight original supports, B(lift(f(v)),N_r)=L_r(v)/s(v). The exact eight-support reconstruction of range(f), together with the complete range identity for e_j, gives R_j={z in H2:for every r!=j, B(lift(e_j(z)),N_r)<=0}. The j-support is zero throughout this full plane; the other seven inequalities describe the entire original bounded region there. Continuity of the native lift and e_j makes these support functions continuous. Consequently a point where all seven are strict has an open H2 neighborhood in R_j.")),
            Paragraph(Text("A zero of a remaining support cannot be an interior point of R_j. Choose an original endpoint on F_j where that support is strictly negative and take its native H2 preimage y. For a point x with that support zero, put Y=lift(e_j(x)), Z=lift(e_j(y)), D=dist(e_j(x),e_j(y))>0 and U=(Z-cosh(D)*Y)/sinh(D). The unit-lift and distance equations give B(U,U)=1 and B(Y,U)=0. Both endpoints lie in the full j-plane, so B(U,N_j)=0. Apply "),
                Ref("D5/S3/Geometry/Hyperideal/ActualRaysJointAngle.actual_rays_joint_angle"),
                Text(" with the coincident directions U,U. Its complete geodesic gamma has lift(gamma(t))=cosh(t)*Y+sinh(t)*U for every real t. This lift stays orthogonal to N_j for every t, including points outside the body, so the complete plane range identity and the embedding homeomorphism of e_j pull gamma back to a continuous H2 line through x. For the active remaining support r, B(U,N_r)=B(Z,N_r)/sinh(D)<0. At every negative t its value on gamma(t) is sinh(t)*B(U,N_r)>0. Such points occur arbitrarily near x and lie outside R_j. Thus interior(R_j) consists exactly of the points where all seven remaining supports are strict, and frontier(R_j) consists exactly of the points in R_j where at least one is zero.")),
            Paragraph(Text("The strict-point construction is simultaneous. For each of the seven remaining supports choose an original endpoint E_r on F_j at which that support is strictly negative; all seven supports are nonpositive at every chosen endpoint. Endpoint existence also follows directly from the exact face hull: if every endpoint were nonnegative for one support, its convex halfspace would contain their whole hull, contradicting the original strict face witness. Let vbar=(sum_r E_r)/7, allowing repeated endpoint choices. Convexity puts this explicit endpoint average in the same original F_j. For each remaining support, linearity writes its value at vbar as the average of seven nonpositive values, one of which is strictly negative. Hence all seven values are strictly negative. The original support readouts and s(vbar)>0 give a native preimage of f(vbar) at which all seven native supports are strict. In particular interior(R_j) is nonempty; no additional simultaneous-witness or length hypothesis is imposed.")),
            Paragraph(Text("The coefficient active-support frontier from the preceding application and the native active-support frontier above give the exact equation frontier(R_j)={z in H2:e_j(z) in f(intrinsicFrontier_Real(F_j))}. Each F_j is compact and closed, and R_j is the intersection of the seven closed native support sublevel sets. In the coefficient affine span, intrinsicInterior_Real(F_j) is F_j minus its intrinsic frontier; in full H2, interior(R_j) is R_j minus its frontier. Injectivity of the same f therefore gives the exact companion equation interior(R_j)={z in H2:e_j(z) in f(intrinsicInterior_Real(F_j))}. These are transports into the actual original supporting planes.")),
            Paragraph(Text("There is also a pointwise homeomorphism h_j:F_j->R_j with e_j(h_j(v))=f(v) for every original face point v. Indeed the restriction of the same f is continuous and injective on compact F_j, and its image lies in the complete range of the isometry e_j. Composing with the continuous inverse of e_j onto its range yields a continuous bijection to R_j; compactness and the Hausdorff native H2 topology give the homeomorphism. This result uses the exact original face and map.")),
            Paragraph(Text("Apply the frontier equation to the preceding cycles T and H. For each displayed closed coefficient edge A of F_j, its H2 edge is h_j(A)={z in R_j:e_j(z) in f(A)}. The entire boundary of each native cap region R_j is the union of h_j(A) over its three displayed closed edges; the entire boundary of each native side region R_j is the union of h_j(A) over its six displayed closed edges, retaining the displayed cyclic labels. The pointwise identity e_j(h_j(v))=f(v) gives e_j(h_j(A))=f(A). The same_body_metric_segments supplier identifies this H3 image f(A) with the full ambient H3 metric-between set of its two native endpoints and supplies its isometric arclength parametrization. The pointwise homeomorphism and original injectivity preserve the distinct cycle vertices, each adjacent-edge singleton intersection and every nonadjacent-edge disjointness statement. These conclusions concern the eight named original cap and side regions and their displayed cycles.")),
            Paragraph(Text("Application: recovering the actual length Gram from native supports and corners. "
                + "Here the starting data are a given set P in the original native H3, four cap normals "
                + "cap_i and four side normals side_i in Real4, and native points p_ij=corner(i,j) "
                + "for all twelve ordered pairs i!=j in {0,1,2,3}. This is a conditional inverse "
                + "direction to the preceding construction from input lengths and a chosen M,f. "
                + "No frame, known cap Gram, or identification of P with that constructed image is assumed. "
                + "Use the same Lorentz form B(u,v)=u0*v0+u1*v1+u2*v2-u3*v3, its matrix "
                + "J=diag(1,1,1,-1), and the original native metric and lift of "),
                Ref("D5/S3/Geometry/Hyperideal/LengthGramMetricSegments"),
                Text(". Its lift_unit and lift_cosh identities give B(lift(p),lift(p))=-1 and "
                    + "B(lift(p),lift(q))=-cosh(dist(p,q)). These are the classical Lorentz metric "
                    + "identities; the argument below applies them with finite-dimensional linear algebra.")),
            Paragraph(Text("Assume B(cap_r,cap_r)=B(side_r,side_r)=1 for every r in {0,1,2,3}, "
                + "and the exact eight-halfspace equality "
                + "P={p in H3: for every r, B(cap_r,lift(p))<=0 and B(side_r,lift(p))<=0}. "
                + "Define the named support traces Fcap_r={p in P:B(cap_r,lift(p))=0} and "
                + "Fside_r={p in P:B(side_r,lift(p))=0}. For every ordered i!=j assume p_ij in P, "
                + "p_ij in Fcap_r iff r=i, and p_ij in Fside_r iff r!=i and r!=j, for every r. "
                + "Finally assume B(cap_r,side_t)=0 whenever r!=t. These are all the support and "
                + "corner premises used here; in particular the two families need not already be "
                + "declared independent. The twelve points are p_01,p_02,p_03,p_10,p_12,p_13,"
                + "p_20,p_21,p_23,p_30,p_31,p_32. Values corner(i,i), if supplied, are unused.")),
            Paragraph(Text("Membership in P makes every support evaluation at p_ij nonpositive. "
                + "Exact incidence then makes B(cap_r,lift(p_ij)) strictly negative for r!=i, "
                + "and B(side_r,lift(p_ij)) strictly negative for r=i or r=j. Fix i!=j and put "
                + "X=lift(p_ij), Y=lift(p_ji). The cap-i evaluation is zero at X and strictly "
                + "negative at Y, so p_ij!=p_ji. Consequently d_ij=dist(p_ij,p_ji)>0 in the "
                + "original native metric. This derives positivity for each paired distance from "
                + "incidence, before any Gram entries are recovered.")),
            Paragraph(Text("Let k,h be the two distinct complementary labels. Evaluate a relation "
                + "alpha*side_k+beta*side_h=0 at lift(p_ih). The side-k evaluation is zero and "
                + "the side-h evaluation is strictly negative, forcing beta=0. Since side_k has "
                + "Lorentz square one, it is nonzero, and alpha=0. Thus side_k,side_h span a "
                + "two-dimensional subspace. Define R={v in Real4:B(side_k,v)=B(side_h,v)=0}, "
                + "the B-orthogonal complement of span(side_k,side_h). The form B is nondegenerate "
                + "because det(J)=-1, so the orthogonal-complement dimension formula gives "
                + "dim(R)=4-2=2.")),
            Paragraph(Text("Both X and Y belong to R by their two complementary side incidences. "
                + "They are independent: evaluating a relation alpha*X+beta*Y=0 against cap_i "
                + "first forces beta=0, and X has Lorentz square -1, so alpha=0. Both cap_i "
                + "and cap_j also belong to R by the offdiagonal cap-side orthogonality. "
                + "Evaluating a relation between these caps at X forces the coefficient of cap_j "
                + "to vanish; cap_i has square one, so the other coefficient vanishes. Each pair "
                + "therefore spans a two-dimensional subspace of the two-plane R. Inclusion and "
                + "equality of dimensions give both span equalities below.")),
            FormulaBlock(new Formula.RelationChain(FormulaRelationOperator.Equal,
                [Call("span", F.Id("X"), F.Id("Y")), F.Id("R"),
                    Call("span", Call("cap", F.Id("i")), Call("cap", F.Id("j")))])),
            Paragraph(Text("The diagonal cap-side evaluations are now forced to be nonzero. "
                + "For any i choose j!=i and write delta_i=B(cap_i,side_i). If delta_i were zero, "
                + "side_i would annihilate both cap_i and cap_j, the latter by the assumed "
                + "offdiagonal orthogonality. The span equality would make B(side_i,Y)=0, "
                + "contradicting its strictly negative value at p_ji. Hence delta_i!=0 for every i. "
                + "The normalized linear functionals phi_i(v)=B(side_i,v)/delta_i and "
                + "psi_i(v)=B(cap_i,v)/delta_i satisfy phi_i(cap_j)=psi_i(side_j)=1 if i=j "
                + "and 0 otherwise. Applying phi_i or psi_i to a linear relation isolates its "
                + "i-th coefficient. Thus all four caps are independent and all four sides are "
                + "independent. If C is the four-by-four matrix with row i equal to cap_i, the "
                + "row-independence criterion gives det(C)!=0 and C invertible. No sign of det(C) "
                + "is required.")),
            Paragraph(Text("For the same arbitrary ordered i!=j set c=cosh(dist(p_ij,p_ji)) "
                + "and s=sqrt(c^2-1). The positive native distance gives c>1 and s>0. The "
                + "original lift identities give B(X,X)=B(Y,Y)=-1 and B(X,Y)=-c.")),
            FormulaBlock(And(
                Eq(F.Id("c"), Call("cosh", Call("dist",
                    Call("corner", F.Id("i"), F.Id("j")),
                    Call("corner", F.Id("j"), F.Id("i"))))),
                Eq(F.Id("s"), Call("sqrt", new Formula.Binary(
                    new Formula.Power(F.Id("c"), F.D(2)), FormulaBinaryOperator.Subtract, F.D(1)))),
                Lt(F.D(1), F.Id("c")), Lt(F.D(0), F.Id("s")))),
            Paragraph(Text("The span equality writes cap_i=a*X+b*Y. Orthogonality at its own "
                + "corner gives -a-b*c=0, so a=-b*c. Its unit square then gives "
                + "b^2*(c^2-1)=1. At the reversed corner its evaluation is "
                + "B(cap_i,Y)=b*(c^2-1)<0. Since c^2-1=s^2>0, this forces b=-1/s and a=c/s. "
                + "Interchanging i and j gives the reversed formula with the same c and s, "
                + "by symmetry of the native distance. Thus the nonpositive support orientation "
                + "selects the actual caps, including their signs.")),
            FormulaBlock(Eq(Call("cap", F.Id("i")), new Formula.Binary(
                Mul(new Formula.Fraction(F.Id("c"), F.Id("s")), F.Id("X")),
                FormulaBinaryOperator.Subtract,
                Mul(new Formula.Fraction(F.D(1), F.Id("s")), F.Id("Y"))))),
            FormulaBlock(Eq(Call("cap", F.Id("j")), new Formula.Binary(
                Mul(new Formula.Fraction(F.Id("c"), F.Id("s")), F.Id("Y")),
                FormulaBinaryOperator.Subtract,
                Mul(new Formula.Fraction(F.D(1), F.Id("s")), F.Id("X"))))),
            Paragraph(Text("Bilinearity now gives B(cap_i,cap_j)=(-c^3+c)/s^2=-c, using "
                + "s^2=c^2-1. This recovers the offdiagonal cap Gram entry from the actual "
                + "native distance. The diagonal entries are one by the unit-cap premise.")),
            FormulaBlock(new Formula.RelationChain(FormulaRelationOperator.Equal,
                [Call("B", Call("cap", F.Id("i")), Call("cap", F.Id("j"))),
                    F.Seq(F.Minus, F.Id("c")),
                    F.Seq(F.Minus, Call("cosh", Call("dist",
                        Call("corner", F.Id("i"), F.Id("j")),
                        Call("corner", F.Id("j"), F.Id("i")))))])),
            Paragraph(Text("Form the actual length vector L in the original six-slot order "
                + "01,02,03,23,13,12, with d_ij=dist(corner(i,j),corner(j,i)). All six entries "
                + "are strictly positive by the paired-corner argument. The use of d_23 in "
                + "slot 3, d_13 in slot 4 and d_12 in slot 5 keeps the original lengthGram convention.")),
            FormulaBlock(Eq(F.Id("L"), Call("tuple",
                Call("d", F.D(0), F.D(1)), Call("d", F.D(0), F.D(2)),
                Call("d", F.D(0), F.D(3)), Call("d", F.D(2), F.D(3)),
                Call("d", F.D(1), F.D(3)), Call("d", F.D(1), F.D(2))))),
            FormulaBlock(All("q", Call("Fin", F.D(6)), Lt(F.D(0), Call("L", F.Id("q"))))),
            Paragraph(Text("Let G=lengthGram(L). Its diagonal entries agree with the cap squares, "
                + "and the recovered offdiagonal entries agree with its six negative hyperbolic cosines; "
                + "reversing an ordered pair uses dist(p_ij,p_ji)=dist(p_ji,p_ij). Since the caps "
                + "are the rows of C, the (i,j)-entry of C*J*transpose(C) is B(cap_i,cap_j). "
                + "Entrywise equality gives the row congruence below, with the invertibility of "
                + "C already derived from the corner evaluations.")),
            FormulaBlock(new Formula.RelationChain(FormulaRelationOperator.Equal,
                [Mul(Mul(F.Id("C"), F.Id("J")), Call("transpose", F.Id("C"))),
                    F.Id("G"), Call("lengthGram", F.Id("L"))])),
            Paragraph(Text("This application recovers the actual metric Gram for given native P, supports "
                + "and ordered corners satisfying the stated hypotheses. Existence of such data from six "
                + "prescribed lengths, inverse identification of P with a source cut-body realization, "
                + "all-face recognition and rigidity remain unresolved. It asserts no global length-domain, "
                + "topology, volume, Schlaefli variation or gluing conclusion.")),
            Paragraph(Text("Application: the derivative of the six original angle formulas. Keep six independent lengths in the existing order 01,02,03,23,13,12, and put x_e=cosh(l_e), sigma_e=sinh(l_e), Delta(x)=-det(G(x)). The parameter domain Omega consists exactly of all l_e>0 and Delta(x)>0, for the existing lengthGram matrix. In each original frame, the two positive source radicands A_e,B_e and source numerator N_e satisfy A_e*B_e-N_e^2=(x_e^2-1)*Delta(x). Since the source cosine is N_e/(sqrt(A_e)*sqrt(B_e)), its strict bounds -1<phi_e<1 are equivalent to Delta(x)>0. This preserves the six original source formulas rather than introducing a substitute angle map.")),
            Paragraph(Text("Define alpha_e(l)=arccos(phi_e(l)). Let J_ef be the e-th component of the Frechet derivative of alpha at l applied to the f-th standard basis vector. Thus rows are output angles and columns are independent input lengths. The preceding native angle-germ application identifies these same alpha_e with the prescribed actual side/side angle germs of the same original body. The source formulas are smooth on Omega because all source radicands and 1-phi_e^2 are strictly positive there.")),
            Paragraph(Text("Differentiating the original signed-cofactor normalization gives K(l)*J(l)=I, where K_ef=sigma_e*W_ef(x)*sigma_f/sqrt(Delta(x)). For x=(a,b,c,d,e,f), the symmetric W has diagonal p0/(a^2-1),p1/(b^2-1),p2/(c^2-1),p3/(d^2-1),p4/(e^2-1),p5/(f^2-1). Its opposite entries W03,W14,W25 are -1. Its remaining upper-triangular entries are W01=c,W02=b,W04=f,W05=e,W12=a,W13=f,W15=d,W23=e,W24=d,W34=c,W35=b,W45=a. Here p0=be+cf+a(bc+ef), p1=ad+cf+b(ac+fd), p2=ad+be+c(ab+ed), p3=be+cf+d(bf+ce), p4=ad+cf+e(af+cd), and p5=ad+be+f(ae+bd). Both symmetric off-diagonal variations are included in the Gram differential; the output slot uses its complementary vertex pair. Contraction of that differential with G on both sides cancels the diagonal normalization terms and supplies the six entries of the inverse identity for every input direction. Invertibility is therefore derived from the original angle formulas.")),
            Paragraph(Text("K is continuous and symmetric on Omega: x_e^2-1 and sqrt(Delta(x)) never vanish. The identity KJ=I makes det(K) nonzero. Coordinatewise cosh and arcosh give a homeomorphism from Omega to the entire six-coordinate domain x_e>1,Delta(x)>0. Applying "), Ref("D5/S3/Geometry/Hyperideal/GramDomainContraction.full_domain_contractible"), Text(" makes Omega contractible, hence connected; no additional radial-preservation or cube-membership premise is used.")),
            Paragraph(Text("At the interior parameter l_e=arcosh(2) for every e, Delta=135 and sigma_e^2=3, so K=W2/sqrt(15). W2 has diagonal 8, opposite entries -1 and all remaining off-diagonal entries 2. For a nonzero real six-vector v, its quadratic form is 3*sum_e(v_e^2)+3*((v0-v3)^2+(v1-v4)^2+(v2-v5)^2)+2*(sum_e v_e)^2>0. This equal-length point supplies only one basepoint; it does not restrict the variable domain.")),
            Paragraph(Text("Positive definiteness is open relative to real symmetric matrices, by upper semicontinuity of the real spectrum and the spectral characterization using eigenvalues. Positive semidefiniteness is closed. For the present everywhere-invertible family K, positive semidefiniteness is equivalent to positive definiteness. Hence the positive-definite locus in Omega is both open and closed, and it is nonempty by the displayed basepoint. Connectedness makes it all of Omega. Finally KJ=I gives J=inverse(K), and the inverse of a positive-definite matrix is positive definite. This proves symmetry and positive definiteness of the actual full six-by-six derivative at every original interior parameter, with no assumed positivity of J.")),
            Paragraph(Text("This application uses the existing full-domain contraction, matrix differential and inverse identities, spectral topology and matrix positivity. It retains all six independent lengths and the exact original interior domain. It asserts no extension through Delta=0 or zero lengths, no variation formula for the measured native volume, and no Schlaefli or geometric co-volume conclusion. Those require the separate volume-variation bridge.")),
            Paragraph(Text("Application: actual reference-simplex integration. For a>=0 let A_a={(y,z): y>=0,z>=0,y+z<=a} and T_a={(x,y,z): x>=0,y>=0,z>=0,x+y+z<=a}. Every integral here is the Bochner integral with the restriction of ordinary product Lebesgue volume. The target E may be any complete real normed space. These are actual measurable closed subsets, not formal face labels or assigned volume values. Both sets are compact, so continuity on them supplies integrability.")),
            Paragraph(Text("For continuous D on T_a, the x-section over (y,z) is [0,a-y-z] when (y,z) belongs to A_a and is empty otherwise. Apply integral_prod_symm to the measurable indicator of T_a, then replace each closed-interval set integral by its interval integral. This gives integral_T_a D=integral_A_a(integral_0^(a-y-z) D(x,y,z) dx) dy dz. The same argument gives the triangle formula integral_A_a H=integral_0^a(integral_0^(a-z) H(y,z) dy) dz. Compactness supplies the joint integrability required by Fubini; section and endpoint conventions are established for these literal sets.")),
            Paragraph(Text("Let P1,P2,P3 and D1,D2,D3 be continuous E-valued functions on T_a. Along every nonempty open coordinate slice, suppose the ordinary derivative of Pi in coordinate i is Di; this includes slices whose other two coordinates lie on the boundary of A_a. The fundamental theorem of calculus gives each directional integral as its top trace minus its coordinate-zero trace. No derivative is required at the slice endpoints, and a zero-length slice imposes no derivative condition. Continuity gives integrability of all six individual top and bottom traces by composition with their affine maps from A_a.")),
            Paragraph(Text("The three top traces must be put into the same parameterization before adding them. The triangle maps (y,z)->(a-y-z,z), (y,z)->(z,y), and their composition (y,z)->(a-y-z,y) preserve the triangle integrals. The reflection identity follows from the one-dimensional substitution integral_comp_sub_left on each literal section; swapping follows from integral_prod_swap. Associativity and commutation of product measures likewise preserve the actual tetrahedron under the coordinate permutations used for its second and third directional formulas. Reparameterize only the second and third top traces; keep each bottom trace in its own coordinate-face chart.")),
            Paragraph(Text("Writing t(y,z)=(a-y-z,y,z), b1(y,z)=(0,y,z), b2(y,z)=(y,0,z), and b3(y,z)=(y,z,0), the resulting identity is integral_T_a(D1+D2+D3)=integral_A_a((P1+P2+P3)(t)-P1(b1)-P2(b2)-P3(b3)). The top coefficient is the sum of the three components. Each coordinate-zero face has its own negative component. This is a coordinate-flux identity with a common planar parameter measure; no surface-area factor or target flux equality is assumed.")),
            Paragraph(Text("The coordinate map from EuclideanSpace R (Fin 3) to R times (R times R), u->(u0,(u1,u2)), is a measurable equivalence preserving actual volume. It is assembled from the existing EuclideanSpace toLp, piFinSuccAbove and piFinTwo measure-preserving equivalences. Thus the reference-simplex integrals also hold for the usual L2 Euclidean volume in those coordinates. This measure statement does not identify the L2 norm with the nested product norm and does not yet identify a parametrized face measure with normalized Hausdorff surface measure.")),
            Paragraph(Text("Parameter differentiation on the fixed reference tetrahedron follows from the dominated differentiation theorem. Fix t0 and r>0. Suppose F(t,z) and D(t,z) are jointly continuous on [t0-r,t0+r] times T_a, and for every t in the open time interval and every z in T_a the derivative of F in t is D(t,z). The compact image of D gives one finite bound C for its norm on that entire product. The constant C is integrable on T_a because this compact set has finite volume; continuity also supplies the required measurable slices and integrability at t0. Applying hasDerivAt_integral_of_dominated_loc_of_deriv_le gives the actual derivative at t0 of integral_T_a F(t,z) as integral_T_a D(t0,z). No integral derivative or domination bound is inserted as an extra hypothesis.")),
            Paragraph(Text("These reference-domain applications combine existing Fubini, interval calculus, product-measure coordinate changes and dominated differentiation. To obtain a moving native-volume formula, their affine change of variables and outward-face coefficients must be assembled with the original twenty-cell decomposition on one common parameter neighborhood, together with uniform bounds, original-density regularity and identification of the integrated reference flux with the physical face measure. The reference identities alone do not assert a variation formula for the measured native body, Schlaefli, a geometric co-volume potential, gluing or completion of the four CFMP sources.")),
            Paragraph(Text("Classification of every arbitrary face of the body, flat-boundary limits, Schlaefli variation, co-volume, gluing and full CFMP completion remain separate obligations. The existing native mass and twelve right-angle truncation applications are retained. The construction reuses the existing geometry and makes no novelty claim for the classical Lorentz formulas.")))));

    private static Formula Statement()
    {
        var l = F.Id("l");
        var v = F.Id("v");
        var c = Call("C", l);
        var r = Call("r", l);
        var image = Call("image", r, c);
        return All("l", F.Id("R6"), Implies(
            All("k", Call("Fin", F.D(6)), Lt(F.D(0), Call("l", F.Id("k")))),
            And(Call("IsCompact", c), In(F.Id("b"), c),
                All("i", Call("Fin", F.D(4)), Lt(Call("Gb", l, F.Id("i")), F.D(0))),
                All("v", F.Id("R4"), Implies(In(v, c), Lt(Call("q", l, v), F.D(0)))),
                Call("ContinuousOn", r, c), Call("InjOn", r, c),
                Call("IsCompact", image), Call("Nonempty", image),
                All("v", F.Id("R4"), Implies(In(v, c),
                    Eq(Call("q", l, Call("r", l, v)), F.Seq(F.Minus, F.D(1))))),
                PhysicalBody(l, c))));
    }

    private static Formula PhysicalBody(Formula l, Formula c)
    {
        var m = F.Id("m");
        var f = F.Id("f");
        var v = F.Id("v");
        var y = F.Id("y");
        var phi = Call("phi01", l);
        var minusOne = F.Seq(F.Minus, F.D(1));
        return Implies(And(Lt(minusOne, phi), Lt(phi, F.D(1))),
            Exists("m", F.Id("Matrix4"), And(
                All("i", Call("Fin", F.D(4)),
                    All("j", Call("Fin", F.D(4)),
                        Eq(Call("B", Call("row", m, F.Id("i")), Call("row", m, F.Id("j"))),
                            Call("G", l, F.Id("i"), F.Id("j"))))),
                Lt(F.D(0), Call("det", m)), Lt(Call("det", Call("G", l)), F.D(0)),
                Exists("f", Call("Maps", c, F.Id("H3")), And(
                    Call("Continuous", f), Call("Injective", f),
                    Call("IsCompact", Call("range", f)), Call("Nonempty", Call("range", f)),
                    All("v", c, Exists("y", F.Id("R4"), And(
                        Eq(y, Call("vecMul", Call("r", l, v), m)),
                        Eq(Call("B", y, y), minusOne), Lt(F.D(0), Call("coord", y, F.D(3))),
                        Eq(Call("coordinates", Call("f", v)), Call("Psi", y))))))))));
    }

    private static Formula Density() => new Formula.Subscript(F.Id("rho"), F.Id("l"));
    private static Formula DensityAt(Formula u) => new Formula.Apply(Density(), [u]);
    private static Formula GramIntegral() => new Formula.Subscript(F.Id("I"), F.Id("l"));
    private static Formula LowerGramIntegral() => new Formula.Subscript(F.Id("lowerGramIntegral"), F.Id("l"));
    private static Formula NativeMass(string measure) => Call("mass", F.Id(measure), Call("range", F.Id("f")));

    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);

    private static DocumentBlock FormulaBlock(Formula p) => new DocumentBlock.DisplayFormula(p);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create(name), domain, body);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula In(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
}
