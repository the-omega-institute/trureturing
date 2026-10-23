using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class ActualRaysJointAngleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual hyperbolic rays and their joint comparison angle.",
        H("Unit tangent rays in the original hyperbolic metric"),
        Blocks(
            Paragraph(Text("Let Rfour be the real four-coordinate space, and let B be the "
                + "space-positive, time-negative Lorentz form. Hthree is the original "
                + "HyperbolicThreeSpace with its hyperbolic distance. Psi is the original "
                + "project map: its horizontal coordinate is (Y0+i*Y1)/(Y3-Y2) and its "
                + "height is 1/(Y3-Y2). Phi is the original inverse lift. The theorem "
                + "ranges over every future unit Y and every pair U,V of Lorentz-unit "
                + "vectors orthogonal to Y, with B(U,V) in the closed interval [-1,1].")),
            Paragraph(Text("Write W(Y,U,t)=cosh(t)Y+sinh(t)U, "
                + "C(c,s,t)=cosh(s)cosh(t)-c sinh(s)sinh(t), and "
                + "K(g,h,s,t)=(s*s+t*t-dist(g(s),h(t))^2)/(2*s*t). "
                + "Angle(g,h) is the function (s,t) mapped to arccos(K(g,h,s,t)). "
                + "Q is the product of the two strictly positive real half-lines; "
                + "NQ is the neighborhood filter at (0,0) within Q. It is a nontrivial "
                + "filter and equals the product of the two right-hand neighborhood "
                + "filters. No restriction is imposed on the ratio of the parameters.")),
            Describe.Lean(
                DescribeId.Create("actual-rays-joint-angle"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/ActualRaysJointAngle.actual_rays_joint_angle"),
                H("Global metric lines and the unrestricted joint limit"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Geometry/ganeabecigneulhofmann2018cones")),
                Blocks(
                    Paragraph(Text("Spatial Cauchy-Schwarz applied to the unit and "
                        + "orthogonality equations gives U3^2 <= Y3^2-1 and hence "
                        + "abs(U3)<Y3. Since abs(sinh(t))<cosh(t), W(Y,U,t) has positive "
                        + "time for every real t. Bilinearity gives B(W,W)=-1. Therefore "
                        + "Psi(W) is defined on the whole real line and Phi(Psi(W))=W. "
                        + "The original metric identity B(Phi(p),Phi(q))=-cosh(dist(p,q)) "
                        + "gives the two-ray distance law. For equal tangent directions, "
                        + "injectivity of cosh on nonnegative reals gives dist(g(s),g(t)) "
                        + "=abs(s-t), proving an actual isometry from the real line.")),
                    Paragraph(Text("Put D=dist(g(s),h(t)), q=abs(s-t), A=(D+q)/2 and "
                        + "E=(D-q)/2. The metric triangle inequalities give q<=D<=s+t "
                        + "for nonnegative s,t. Define S(x)=dslope(sinh,0,x); thus "
                        + "S(0)=1, x*S(x)=sinh(x), and S is continuous at zero. "
                        + "For positive s,t, the cosh distance law and the addition "
                        + "identities give K=1-(1-c)S(s)S(t)/(S(A)S(E)). The denominator "
                        + "is positive, including E=0. Metric continuity makes A,E tend "
                        + "jointly to zero, so this expression extends continuously "
                        + "with value c at the origin. Continuity of arccos gives the "
                        + "stated angle limit, including c=1 and c=-1. The proof never "
                        + "divides by D, A, E or 1-c; D=0 is included.")),
                    Paragraph(Text("For the original Section 66 radial realization, "
                        + "Y is the lift of a point of the same image and tangent "
                        + "directions must satisfy the displayed unit and orthogonality "
                        + "conditions. This result provides metric rays and their angle. "
                        + "It does not identify inward face germs or recover the original "
                        + "body from supporting halfspaces. Normal normalization, "
                        + "same-body face membership, and the six original and twelve "
                        + "truncation dihedral angles remain separate mathematical "
                        + "obligations. The full realization problem retains all six "
                        + "positive lengths and all six strict source cosine conditions.")),
                    Paragraph(Text("The classical cosh-sinh ray formula is recorded in "
                        + "Appendix A, Theorem 6, equation (38) of the cited supplement "
                        + "on [0,1], with time-first coordinates. The construction here "
                        + "establishes the global original-metric contract and derives "
                        + "the joint limit directly; it makes no novelty claim for the "
                        + "classical geometry."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var y = F.Id("Y"); var u = F.Id("U"); var v = F.Id("V");
        var g = F.Id("g"); var h = F.Id("h"); var s = F.Id("s"); var t = F.Id("t");
        var c = Call("B",u,v); var r = F.Id("R"); var zero = F.D(0);
        var d = Call("dist",Call("apply",g,s),Call("apply",h,t));
        var hypothesis = And(Eq(Call("B",y,y),F.Seq(F.Minus,F.D(1))),
            Lt(zero,Call("coord",y,F.D(3))), Eq(Call("B",u,u),F.D(1)),
            Eq(Call("B",v,v),F.D(1)), Eq(Call("B",y,u),zero), Eq(Call("B",y,v),zero),
            Le(F.Seq(F.Minus,F.D(1)),c), Le(c,F.D(1)));
        var conclusion = And(Call("Isometry",g),Call("Isometry",h),
            Eq(Call("apply",g,zero),Call("Psi",y)),Eq(Call("apply",h,zero),Call("Psi",y)),
            All("t",r,Eq(Call("Phi",Call("apply",g,t)),Call("W",y,u,t))),
            All("t",r,Eq(Call("Phi",Call("apply",h,t)),Call("W",y,v,t))),
            All("s",r,All("t",r,Eq(Call("cosh",d),Call("C",c,s,t)))),
            All("s",r,All("t",r,Implies(And(Le(zero,s),Le(zero,t)),
                And(Le(Call("abs",F.Seq(s,F.Minus,t)),d),Le(d,F.Seq(s,F.Plus,t)))))),
            Call("Tendsto",Call("Angle",g,h),F.Id("NQ"),Call("nhds",Call("arccos",c))));
        return All("Y",F.Id("Rfour"),All("U",F.Id("Rfour"),All("V",F.Id("Rfour"),
            Implies(hypothesis,Exists("g",Call("Maps",r,F.Id("Hthree")),
                Exists("h",Call("Maps",r,F.Id("Hthree")),conclusion))))));
    }
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),domain,body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(name),domain,body);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name),[.. args]);
    private static Formula And(params Formula[] clauses)
    {
        var result=clauses[^1];
        for(var i=clauses.Length-2;i>=0;i--) result=new Formula.Logic(clauses[i],FormulaLogicOperator.And,result);
        return result;
    }
    private static Formula Implies(Formula left,Formula right) => new Formula.Logic(left,FormulaLogicOperator.Implies,right);
    private static Formula Lt(Formula left,Formula right) => new Formula.Relation(left,FormulaRelationOperator.LessThan,right);
    private static Formula Le(Formula left,Formula right) => new Formula.Relation(left,FormulaRelationOperator.LessThanOrEqual,right);
    private static Formula Eq(Formula left,Formula right) => new Formula.Relation(left,FormulaRelationOperator.Equal,right);
}
