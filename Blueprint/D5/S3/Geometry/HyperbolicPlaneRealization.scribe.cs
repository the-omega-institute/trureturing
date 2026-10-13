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
