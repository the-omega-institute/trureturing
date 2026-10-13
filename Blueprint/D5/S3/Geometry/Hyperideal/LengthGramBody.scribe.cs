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
            Paragraph(Text("The angle and endpoint-distance applications do not identify the full two-endpoint ridge range or prove angle constancy at every ridge point. Complete face incidence, relabeling isometries, flat-boundary limits, Schlaefli variation, co-volume, gluing and full CFMP completion remain separate obligations. The existing native mass and twelve right-angle truncation applications are retained. The construction reuses the existing geometry and makes no novelty claim for the classical Lorentz formulas.")))));

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
