using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class HyperbolicPlaneRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full actual-metric realization of original Lorentz supporting planes.",
        H("Spacelike supporting planes in the original hyperbolic metric"),
        Blocks(
            Paragraph(Text("Write B(X,Y)=X0*Y0+X1*Y1+X2*Y2-X3*Y3 on R4. "
                + "H2 is Mathlib UpperHalfPlane with its hyperbolic distance and H3 is "
                + "HyperbolicThreeSpace with the repository's existing hyperbolic distance. "
                + "For p with horizontal coordinate x+i*y and height h>0, Phi(p) is the "
                + "original LengthGramMetricSegments.lift: "
                + "(x/h,y/h,(x*x+y*y+h*h-1)/(2*h),(x*x+y*y+h*h+1)/(2*h)). "
                + "Pi(N) denotes exactly {p in H3 : B(Phi(p),N)=0}. Maps denotes functions, "
                + "Range their complete image, and Isometry refers to these actual metrics.")),
            Describe.Lean(
                DescribeId.Create("positive-time-of-pair"),
                DeclarationHandle.Create("D5/S3/Geometry/HyperbolicPlaneRealization.positive_time_of_pair"),
                H("A negative Lorentz pairing selects the future unit sheet"),
                StatementSource.FromAuthor(F.Disp(PositiveTimeStatement())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Geometry/cannonfloydkenyonparry1997hyperbolic")),
                Blocks(
                    Paragraph(Text("For X,Y in R4 write Coord(X,k)=Xk, t=X3 and s=Y3. "
                        + "Both vectors are unit timelike: B(X,X)=B(Y,Y)=-1. The hypotheses "
                        + "also require t>0 and B(X,Y)<0. Then s>0, so Y lies on the same "
                        + "future unit sheet as X. Neither vector is assumed to be a "
                        + "previously realized hyperbolic point.")),
                    Paragraph(Text("Put c=X0*Y0+X1*Y1+X2*Y2. Spatial Cauchy-Schwarz gives "
                        + "c*c <= (t*t-1)*(s*s-1). The unit equations imply t*t>=1 and "
                        + "s*s>=1. If s<=0, then t*s<=0 and the strict pairing condition "
                        + "gives c<t*s<=0. Thus c*c>(t*s)*(t*s). But "
                        + "(t*t-1)*(s*s-1)<(t*s)*(t*s), contradicting Cauchy-Schwarz.")),
                    Paragraph(Text("The supporting-plane construction applies this criterion "
                        + "to a future unit X and its Lorentz reflection Y=R(X). More "
                        + "generally, a Lorentz-pairing-preserving linear map that sends "
                        + "one future unit reference vector to the future sheet preserves "
                        + "that sheet for every future unit input: pair its image with "
                        + "the image of the reference vector and use the negative "
                        + "unit-sheet pairing. The criterion supplies the positive time "
                        + "coordinate needed by the original inverse-coordinate map. "
                        + "It alone asserts no ambient isometry construction.")),
                    Paragraph(Text("Application: full ambient extension between given original realizations. Retain six arbitrary positive lengths in the original order 01,02,03,23,13,12. A vertex permutation sigma sends new labels to old labels; P_sigma(v)_i=v_sigma(i) and l_sigma(q) is the old length at the unordered slot joining sigma(i),sigma(j), where i,j are the endpoints of q. Suppose M/f and N/g are already given realizations of C(l) and C(l_sigma), with their exact Gram equations, nonsingular frames, and future-unit radial-coordinate contracts in the existing native H3. Put A(Y)=P_sigma(Y times inverse(M)) times N. Matrix inversion and coordinate reindexing give its inverse Ainv(Z)=P_sigma_inverse(Z times inverse(N)) times M and preservation of every Lorentz pairing.")),
                    Paragraph(Text("The original coefficient barycenter b_i=1/4 belongs to C(l). Exact radial-coordinate transport sends lift(f(b)) to lift(g(P_sigma(b))), giving one future reference image. For every native p, pair A(lift(p)) with that reference image: pairing preservation and the existing lift_cosh identity give a strictly negative pairing, and the criterion above gives positive time. Apply it also to Ainv using the reversed reference. The original projection and lift_of_coordinates then construct mutually inverse maps of all native H3. The preserved lift pairing and strict monotonicity of cosh on nonnegative distances prove a full ambient isometry E, with lift(E(p))=A(lift(p)), E(f(v))=g(P_sigma(v)), and E applied to the complete range(f) equal to range(g). This establishes the ambient extension, rather than only an isometry between the body images.")),
                    Paragraph(Text("Under the original six-positive-length and six-strict-source-cosine assumptions, shared_radial_body selects one original M/f and this ambient extension then applies to every permutation and every already supplied valid nonsingular N/g. The quantifier over the second realization is conditional; its existence is not asserted here. Neither a positive determinant for N nor an orientation-preserving E is required. Positive-orientation normalization after odd relabeling, strict-cosine naturality for the new length tuple, and automorphisms of a fixed asymmetric length model are not conclusions of this application."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supporting-plane-isometry"),
                DeclarationHandle.Create("D5/S3/Geometry/HyperbolicPlaneRealization.supporting_plane_isometry"),
                H("Every spacelike supporting plane is an entire isometric hyperbolic plane"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Geometry/cannonfloydkenyonparry1997hyperbolic")),
                Blocks(
                    Paragraph(Text("For B(N,N)>0 put r=sqrt(B(N,N)), and choose s=r when N1>=0 "
                        + "and s=-r otherwise. With E1=(0,1,0,0) put M=N+s*E1. Then "
                        + "s is nonzero, s*s=B(N,N), s*N1>=0, and "
                        + "d=B(M,M)=2*(B(N,N)+s*N1)>0. The auxiliary Lorentz reflection "
                        + "R(X)=X-2*B(X,M)/d*M preserves B, satisfies R(R(X))=X, and "
                        + "B(R(X),N)=-s*X1. Involution directly applies the pinned Mathlib "
                        + "Module.involutive_preReflection to the real linear functional "
                        + "f(X)=2*B(X,M)/d, with f(M)=2; preReflection M f is exactly R. "
                        + "Linearity uses the original lorentz_linear theorem. "
                        + "This construction covers both N2=N3 and "
                        + "N2!=N3; it never divides by N2-N3.")),
                    Paragraph(Text("The reflection preserves the future unit sheet. Indeed "
                        + "B(X,R(X))=-1-2*B(X,M)^2/d<0 for B(X,X)=-1. If X3>0 "
                        + "and a unit timelike Y had Y3<=0, finite-dimensional Cauchy-Schwarz "
                        + "would contradict B(X,Y)<0. Apply this to Y=R(X). Thus the original "
                        + "projection Psi(Y)=((Y0+i*Y1)/(Y3-Y2),1/(Y3-Y2)) is defined: "
                        + "future_den supplies Y3-Y2>0. The original lift_of_coordinates "
                        + "supplies Phi(Psi(Y))=Y.")),
                    Paragraph(Text("Embed z=u+i*v from H2 vertically as vmap(z)=(u,0,v) "
                        + "in H3 and define e(z)=Psi(R(Phi(vmap(z)))). The existing H2 "
                        + "cosh_dist' formula gives B(Phi(vmap(z)),Phi(vmap(w)))="
                        + "-cosh(dist_H2(z,w)); the original lift_cosh gives the corresponding "
                        + "H3 equation. Reflection preserves their pairing, and strict "
                        + "monotonicity of cosh on nonnegative distances proves Isometry(e).")),
                    Paragraph(Text("For surjectivity, take any p with B(Phi(p),N)=0. "
                        + "Y=R(Phi(p)) is future unit, and the reflection identity plus its "
                        + "involution imply Y1=0 because s!=0. Set "
                        + "z=Y0/(Y3-Y2)+i/(Y3-Y2). Its imaginary part is strictly positive. "
                        + "The original inverse-coordinate theorem gives Phi(vmap(z))=Y; "
                        + "involution and lift_injective then give e(z)=p. Conversely every "
                        + "e(z) is orthogonal to N because Phi(vmap(z))1=0. Thus the range "
                        + "equality includes every point of the original plane, without a "
                        + "surjectivity or isometry assumption.")),
                    Paragraph(Text("The source attribution concerns classical hyperbolic "
                        + "model transport and Lorentz geometry: Cannon-Floyd-Kenyon-Parry "
                        + "(1997), Theorem 9.3 and page 80, then Section 10, Theorem 10.1 "
                        + "on page 82 (including upper-sheet preservation) and the distance "
                        + "lemma on page 83. The exact realization in these existing repository "
                        + "types is a repository derivation. No mathematical novelty is claimed.")),
                    Paragraph(Text("For the later original CFMP sections 65-66 application, "
                        + "retain one and the same supplied Gram frame m, radial map and "
                        + "map f from cutBody(l). The six positive lengths remain in order "
                        + "(01,02,03,23,13,12), with all six strict source cosine inequalities "
                        + "retained in that application. For each already identified spacelike "
                        + "normal N in this original frame, this theorem identifies its exact "
                        + "zero locus as an actual hyperbolic plane. The reflection is an "
                        + "auxiliary parametrization; it does not replace m, f or their body. "
                        + "The corresponding halfspace intersection equality uses the existing "
                        + "normal correspondence and coefficient normalization, not a new "
                        + "tetrahedron. This generic theorem assumes no tetrahedron or "
                        + "cosine data and does not itself verify those normal correspondences.")),
                    Paragraph(Text("Application: one explicit chart for an original coefficient triangle. Fix the same six-length Gram frame m, with det(m) nonzero and B(row_i(m),row_j(m))=lengthGram(l)_{ij}. Write xi(q)=a+q0*b+q1*c for q in R2, with sum(a)=1, sum(b)=sum(c)=0, and injective tangent map q |-> q0*b+q1*c. Let K be a nonempty measurable parameter set on which r(q)=-B(u(q),u(q))>0 and d(q)=u3(q)-u2(q)>0, where u(q)=xi(q) times m. When using the original body map f, also require xi(K) to lie in cutBody(l) and use its supplied radial-coordinate contract. The Gram pullback identity gives B(u,u)=gramQuadratic(l,xi); the original lift_of_coordinates and radial formula then give lift(f(xi(q)))=u(q)/sqrt(r(q)). No second realization is selected. For an internal triangle in the original twenty-cell subdivision, take a to be its original coefficient barycenter, b=P-a and c=Q-a for its two retained original endpoints P,Q, and K={q0>=0,q1>=0,q0+q1<=1}; the displayed positivity and tangent-injectivity conditions remain the applicability requirements.")),
                    Paragraph(Text("Choose a nonzero N orthogonal to a*m, b*m and c*m by the kernel of their three Lorentz linear functionals on R4. A timelike witness u(q) from the same nonempty K proves B(N,N)>0. Indeed W=T3*N-N3*T has W3=0, and orthogonality gives T3^2*B(N,N)=B(W,W)+(-B(T,T))*N3^2. The right side is nonnegative; equality would force N=0 by the original null-orthogonality result after positive normalization of T. Apply the original adapted reflection once, retaining its same vector A=N+s*E1, B(A,A)>0, and linear reflection R throughout all subsequent constructions. Its involution and B(RX,N)=-s*X1 imply (R*u(q))1=0 on the entire affine parameter plane.")),
                    Paragraph(Text("Put v(q)=R*u(q), rho(q)=sqrt(r(q)), delta(q)=v3(q)-v2(q), and g(q)=(v0(q)/delta(q),rho(q)/delta(q)). The original future-sheet criterion gives delta(q)>0 wherever r(q)>0 and d(q)>0, so g(q) is an actual upper-half-plane point. Let V(z) be the original vertical inclusion (Re(z),0,Im(z)), and define e(z)=project(R(lift(V(z)))). The original lift and project equations give lift(e(z))=R(lift(V(z))); preservation of the Lorentz pairing and the original H2/H3 cosh distance formulas prove that this e is an isometry for the actual metrics. Direct coordinates give lift(V(g(q)))=v(q)/rho(q). When the original f-contract above is supplied, involution and lift injectivity therefore give e(g(q))=f(xi(q)) for the very same original f and every q in K. The vector A is the same witness used for the coefficient section and the native isometry.")),
                    Paragraph(Text("Drop the identically zero coordinate v1, retaining coordinates (v0,v2,v3). On these triples the linear section is S(w)=sum((R(insert(w)))*inverse(m)), where insert(w)=(w0,0,w1,w2). Inverting m and R shows S(v(q))=1 and S applied to either constant parameter tangent is zero. The two tangents are independent by the original tangent injectivity and invertibility. Thus the augmented determinant C=det[[v0,v2,v3],[partial_0(v0),partial_0(v2),partial_0(v3)],[partial_1(v0),partial_1(v2),partial_1(v3)]] is constant and nonzero. This section also removes the projective scaling ambiguity: equality of g-values first identifies normalized triples, and applying S recovers their scale and hence the original parameter point.")),
                    Paragraph(Text("The displayed g is differentiable at every point of the positive open region r>0,d>0, with det(Dg)=C/(sqrt(r)*delta^2). Its imaginary coordinate is sqrt(r)/delta, hence abs(det(Dg))/(Im(g))^2=abs(C)/(sqrt(r))^3. Equal-dimensional weighted change of variables applies to every measurable K in this region, including the full closed parameter triangle, and gives the nonnegative integral identity integral over g(K) of y^(-2) dxdy = integral over K of abs(C)/(sqrt(r(q)))^3 dq0dq1. No finiteness assumption or removal of the triangle boundary is needed. The native two-dimensional calibration identifies H2 normalized Hausdorff two-measure with dxdy/y^2, and the same actual isometry e sends this measure to normalized native H3 Hausdorff two-measure restricted to its plane. Complex.volume_preserving_equiv_pi identifies the Complex coordinate integral with product volume on Fin 2 -> Real; it asserts volume preservation without changing the coordinate norm. Thus the displayed integral is exactly the native surface area of e(g(K)), and, under the original f-contract and e(g(q))=f(xi(q)), the native surface area of the original f(xi(K)). The result allows the full closed parameter triangle and zero or infinite measure. A varying-field flux and a moving-volume formula remain separate obligations.")),
                    Paragraph(Text("Under the same full coefficient-section, tangent-injectivity and pointwise original-map contracts, compactness of K makes the native surface area finite. Indeed r(q) is continuous and strictly positive on K, so abs(C)/(sqrt(r(q)))^3 is continuous on K. ContinuousOn.integrableOn_compact and Integrable.lintegral_lt_top give finiteness of its nonnegative integral. If K also has positive two-dimensional parameter volume, the nonzero determinant C makes this density strictly positive at every point of K. Measurability and setLIntegral_pos_iff then give strictly positive native area of that same original f(xi(K)). The full closed reference triangle {q0>=0,q1>=0,q0+q1<=1} is compact and has positive parameter volume: it is a closed subset of [0,1]^2 and contains the nonempty open triangle q0>0,q1>0,q0+q1<1. Thus its original native image has area strictly between zero and infinity whenever the preceding full geometric chart conditions hold throughout it. The conditions above state the generic compact-triangle criterion. Native flux for a varying field and moving-volume variation still require their own identities.")),
                    Paragraph(Text("These conditions hold for all sixty internal face occurrences of the original twenty-cell decomposition, using one supplied Gram frame M and its same original radial realization f. Retain six positive lengths, det(M)!=0, the complete equation B(M_i,M_j)=G_(i,j), and the original future-unit radial-coordinate contract for f on cutBody(l). For n in Fin(20), write V_j=LengthGramSideTrace.vertices(l,n,j), b=V_0, and, for i in Fin(3), let k_0,k_1 be the two increasing labels in {1,2,3} other than i+1. Put d_0=V_(k_0)-b, d_1=V_(k_1)-b and xi(q)=b+q0*d_0+q1*d_1 on the full closed reference triangle K. Every original vertex belongs to cutBody(l); convexity places xi(K) in that same body. The original cells are affinely independent, so the two selected directions give an injective tangent map. Their coefficient sums are zero, while the sum of b is one.")),
                    Paragraph(Text("The original negative Gram quadratic and the same f-contract give B(xi(q)M,xi(q)M)<0 and positive time and denominator throughout K. At q=0, the adapted-plane construction chooses one reflection vector A for this face. The same A supplies the native plane isometry, the coefficient section, independent reflected tangents, positive r and delta on all of K, and exact equality e(g(q))=f(xi(q)). Thus the compact positive-area application gives 0<H^2_native({f(xi(q)):q in K})<infinity for every n and i; the set is the image of this same original f, including the triangle boundary. No facewise positivity, rank, section or containment hypothesis is added. Moreover LengthGramBody.shared_radial_body supplies one common M and continuous injective f under -1<phi_01<1, with all sixty conclusions referring to that one realization. The full geometric-realization objective retains its six strict source cosine conditions. These native area statements do not identify varying-field flux densities or moving-volume variation, and do not establish the Schlaefli identity.")),
                    Paragraph(Text("The same native surface-area formula also transports variable nonnegative weights. Keep the original face data above, set s(q)=sqrt(r(q)), and write F={f(xi(q)):q in K} and J(q)=abs(C)/s(q)^3. For every weight w:H3 -> [0,infinity] (nonnegative extended reals), the lower integral of w over F with respect to normalized native Hausdorff two-measure equals the lower integral over the full closed K of J(q)*w(f(xi(q))) with respect to product Lebesgue measure. The equality permits an infinite value and does not require w to be measurable. Values assigned to f(xi(q)) outside K are irrelevant; the parameter integral is restricted to K. In particular this applies for each n in Fin(20) and i in Fin(3) of the same original decomposition, using the same supplied M/f, with J strictly positive on every point of its closed parameter triangle.")),
                    Paragraph(Text("To derive the weighted identity, retain the same adapted reflection, native isometry e and upper-half-plane chart g, so e(g(q))=f(xi(q)) for all q in K. The existing native two-dimensional calibration and isometric Hausdorff transport give the lower integral over e(g(K)) of w as the lower integral over g(K) of w(e(z)) dxdy/y^2. UpperHalfPlane.volume_def supplies the height density, and Complex.volume_preserving_equiv_pi passes to the two real coordinates without changing either native metric. The chart has a within-K derivative and is injective on K by the same sum-one section and tangent-rank conditions. Its image is measurable by measurable_image_of_fderivWithin; the inverse coordinate equalities identify the image of g even though no global measurability of a chosen extension of g is needed. The pinned lintegral_image_eq_lintegral_abs_det_fderiv_mul then gives the density abs(det(Dg))/(Im(g))^2=J(q), multiplied by that same w(e(g(q))). The finite measurable height density and setLIntegral_comp_emb preserve this argument for arbitrary nonnegative extended-real weights.")),
                    Paragraph(Text("For each original internal occurrence, the reflected affine section, tangent injectivity, positive radius and positive reflected denominator used in this argument are derived from its retained original vertices and the same M/f contract. They hold on all of K, including its edges and vertices. Choosing the chart point through the explicit reflected-coordinate equations yields the literal equality e(g(q))=f(xi(q)); a fresh independent choice of a supporting-plane isometry is unnecessary. This identifies the complete original face image in the weighted integral and retains one common realization for all sixty occurrences. The density is unoriented because it contains abs(C). Signed field flux, outward-normal identification, cancellation of physical fluxes and moving-volume variation require further arguments; this lower-integral identity alone makes no integrability or Schlaefli assertion.")),
                    Paragraph(Text("The same original face admits a signed scalar change of variables. Keep K, F, J and the same supplied M/f above; write mu for normalized native Hausdorff two-measure. There is one globally measurable map P:R2 -> H3, independent of the scalar function, with P(q)=f(xi(q)) on the entire closed K. J is globally measurable and nonnegative, and strictly positive on K. The exact pushforward identity is P_*((Lebesgue restricted to K) with density J)=mu restricted to F. Consequently all quantities concern the same original face range, including its edges and vertices; no global measurability assumption on the supplied f is needed.")),
                    Paragraph(Text("For this pushforward, retain the same reflection and plane isometry e. Form P by applying e to UpperHalfPlane.ofComplex of the complex point corresponding to chart(v+a*q). The complex chart is globally measurable by real arithmetic and sqrt. The totalized ofComplex is measurable by splitting at the open set of positive imaginary part: there it returns the given complex point as an upper-half-plane point, and on the complement it returns one fixed chosen point. No global continuity of this totalization is asserted. On K, the explicit positive-height coordinate equations identify P(q) with the same f(xi(q)). Testing the completed weighted lower-integral identity against arbitrary measurable nonnegative functions, using lintegral_map and withDensity, gives the pushforward equality by Measure.ext_of_lintegral.")),
                    Paragraph(Text("For every real-valued phi integrable on F with respect to mu, the function q -> J(q)*phi(P(q)) is integrable on K, and the real integral of phi over F equals the real integral of J(q)*phi(P(q)) over K. This source integrability is a conclusion: transport target integrability through the measurable P, then use the withDensity integrability equivalence and toReal(ofReal(J))=J. The signed identity follows from integral_map and the withDensity integral formula. Thus it is a signed scalar substitution for each of the sixty original internal occurrences with one fixed supplied M/f. The positive unoriented J supplies no outward normal or physical flux sign; actual field-normal densities, physical flux cancellation, moving volume and Schlaefli still require further arguments.")),
                    Paragraph(Text("Actual dihedral angles, the joint comparison-angle limit, "
                        + "the full eight-plane tetrahedron realization, inverse arbitrary "
                        + "tetrahedron realization and rigidity, volume, gluing and genus "
                        + "remain outside this theorem. The full four-source CFMP goal, "
                        + "sections 1-125 including 42.3 and 122.3, is not completed here."))),
                DescribeRole.Theorem))));

    private static Formula PositiveTimeStatement()
    {
        var x = F.Id("X"); var y = F.Id("Y");
        return All("X", F.Id("R4"), All("Y", F.Id("R4"),
            Implies(Eq(Call("B", x, x), F.Seq(F.Minus, F.D(1))),
                Implies(Eq(Call("B", y, y), F.Seq(F.Minus, F.D(1))),
                    Implies(Lt(F.D(0), Call("Coord", x, F.D(3))),
                        Implies(Lt(Call("B", x, y), F.D(0)),
                            Lt(F.D(0), Call("Coord", y, F.D(3)))))))));
    }

    private static Formula Statement()
    {
        var n = F.Id("N"); var e = F.Id("e");
        return All("N", F.Id("R4"), Implies(
            Lt(F.D(0), Call("B", n, n)),
            Exists("e", Call("Maps", F.Id("H2"), F.Id("H3")),
                And(Call("Isometry", e), Eq(Call("Range", e), Call("Pi", n))))));
    }
    private static Formula All(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, b);
    private static Formula Exists(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), d, b);
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(F.Id(n), [.. a]);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
}
