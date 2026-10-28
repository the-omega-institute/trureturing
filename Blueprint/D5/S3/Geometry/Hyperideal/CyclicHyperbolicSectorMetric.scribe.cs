using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class CyclicHyperbolicSectorMetricDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A capped angular comparison controls all original finite chains in numbered hyperbolic sectors.",
        H("Original chains in cyclic hyperbolic sectors"),
        Blocks(
            Paragraph(Text("Let H3 denote HyperbolicThreeSpace with its original metric and let Phi be LengthGramMetricSegments.lift, with Lorentz coordinates (x,y,u,v) of signature (1,1,1,-1). For 0<alpha<pi, S(alpha) is the actual closed subset defined by y>=0 and cos(alpha)*y-sin(alpha)*x<=0. It inherits the original H3 distance and includes the axis x=y=0. The upper face is the equality cos(alpha)*y-sin(alpha)*x=0 within S(alpha); the lower face is y=0 within S(alpha). These are complete faces, including the axis.")),
            Paragraph(Text("Choose any natural number n and widths alpha(i) in (0,pi), indexed by Fin(n+1). Set b(i)=sum over k<i of alpha(k), and A=sum over all k of alpha(k). The datum G(alpha) is cyclicDatum: its numbered source piece i is S(alpha(i)), its generator i goes to the next cyclic index, and its actual partial isometry rotates the complete upper face by -alpha(i) to the next complete lower face. All rotations preserve the actual axis. The source is the disjoint union of these actual subsets; equal underlying H3 coordinates in different source tags are distinct representatives. The relation, paid moves, forward and backward zero-cost seam moves, and distance infimum are exactly those of FiniteOrbitChainMetric.Datum.")),
            Paragraph(Text("For a point p with Phi(p)=(x,y,u,v), set r(p)=arsinh(norm(x+iy)), z(p)=arsinh(u/cosh(r(p))), and t(p)=arg(x+iy). Within S(alpha), t(p) lies in [0,alpha]. On the axis it is zero. Write C(r,z,t) for the actual H3 point whose lift is (sinh(r)*cos(t),sinh(r)*sin(t),cosh(r)*sinh(z),cosh(r)*cosh(z)). Then p=C(r(p),z(p),t(p)); at r=0 the point C is independent of its last argument.")),
            Paragraph(Text("For tagged p=(i,p0), put Theta(p)=b(i)+t(p0). For tagged p,q define dbar(p,q)=min(pi,norm([Theta(q)-Theta(p)] in AddCircle(A))), and L(alpha,p,q)=dist_H3(C(r(p0),z(p0),0),C(r(q0),z(q0),dbar(p,q))). This is comparisonLength. The scalar angular circle retains the period A even when A exceeds 2pi. No new three-dimensional quotient or distance is introduced.")),
            Describe.Lean(DescribeId.Create("cyclic-sector-distance-lower-bound"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/CyclicHyperbolicSectorMetric.cyclic_sector_distance_lower_bound"),
                H("Every original chain dominates the angular comparison"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every choice of the widths and every pair of original tagged representatives, ofReal(L(alpha,p,q)) is at most the literal original cost infimum delta(G(alpha),p,q). The comparison therefore bounds every finite original chain between them, with arbitrary paid moves, repeated seams, inverse transitions, winding and axis visits. No restriction on total angle A, chain length or radial and axial coordinates is imposed.")),
                    Paragraph(Text("Fix the first endpoint p and define h(theta)=min(pi,norm([theta-Theta(p)] in AddCircle(A))). Map each point x in source piece i to C(r(x),z(x),h(b(i)+t(x))). The reverse triangle inequality for the scalar circle norm, followed by the real truncation, gives abs(h(s)-h(t))<=abs(s-t). Two angles in the same actual source sector differ by less than pi. The exact cylindrical distance identity is cosh(dist(C(r,z,s),C(R,Z,t)))=cosh(r)*cosh(R)*cosh(z-Z)-sinh(r)*sinh(R)*cos(s-t). Monotonicity of cosine on [0,pi] and of hyperbolic cosine on nonnegative distances shows that this map does not increase distances within any source piece.")),
                    Paragraph(Text("A non-axis upper-face point has local angle alpha(i), and its rotated lower-face representative has local angle zero. The cumulative angles agree in AddCircle(A) across every designated seam, including the closing seam. The radial and axial coordinates are preserved by the actual rotations. At axis points the cylindrical image ignores the angle. Thus the maps on all numbered pieces agree on every original forward or inverse identification.")),
                    Paragraph(Text("Induction on the original Chain constructors bounds the image distance by the accumulated cost: a paid move uses the source nonexpansion and triangle inequality, while either seam move leaves the image fixed. Taking the original infimum gives the displayed bound. Because the fold depends on p, the argument does not assert that a single fixed H3 map realizes all pairwise capped angular distances.")),
                    Paragraph(Text("This result is a lower comparison. It does not construct a minimizing original chain or prove equality with L. Short-angle segment subdivisions and the opposite-ray axis branch are further upper-bound obligations. To identify this model with an original CFMP edge star one must also construct its simultaneous axis coordinates, original face transports, dihedral-angle correspondence, complete orbit correspondence and a confinement radius for competing chains. Those identifications are not assumptions silently discharged by the sector model."))))));

    private static Formula Statement()
    {
        var a = F.Id("alpha"); var p = F.Id("p"); var q = F.Id("q");
        var index = Call("Fin", F.Seq(F.Id("n"), F.Plus, F.D(1)));
        var widths = All("i", index, And(Lt(F.D(0), App(a, F.Id("i"))),
            Lt(App(a, F.Id("i")), F.Id("pi"))));
        return All("n", F.Id("Nat"), All("alpha", Call("Maps", index, F.Id("Real")),
            Implies(widths, All("p", Call("Source", a), All("q", Call("Source", a),
                Le(Call("ofReal", Call("L", a, p, q)), Call("delta", Call("G", a), p, q)))))));
    }
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(F.Id(s), [.. xs]);
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}
