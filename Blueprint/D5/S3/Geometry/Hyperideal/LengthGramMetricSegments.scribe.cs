using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LengthGramMetricSegmentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Metric segments of the same frozen six-length radial body.",
        H("The original coefficient segment and every ambient between-point"),
        Blocks(
            Paragraph(Text("Fix the six strictly positive lengths l in the original order "
                + "(01,02,03,23,13,12). C(l), q(l,v), radial(l,v), and the space-positive, "
                + "time-negative Lorentz form B are exactly LengthGramBody's definitions. "
                + "Keep one concrete matrix m and one injective map f from C(l) into the actual "
                + "hyperbolic upper half-space H3. No replacement congruent tetrahedron is chosen. "
                + "The displayed radial-coordinate condition is precisely the supplied witness; "
                + "Psi(y) has horizontal coordinate (y0+i*y1)/(y3-y2) and height 1/(y3-y2). "
                + "Positive time is part of the contract, and all distances below are the "
                + "hyperbolic metric on HyperbolicThreeSpace, not the Euclidean coordinate metric.")),
            Paragraph(Text("For lambda,mu in C(l), write D=dist(f(lambda),f(mu)). "
                + "ImageSegment(l,f,lambda,mu) is the set of all f(v), where v is in C(l) "
                + "and its original coefficient vector belongs to the closed affine segment "
                + "[lambda,mu]. Between(p,q) is the set of every ambient z in H3 satisfying "
                + "dist(p,z)+dist(z,q)=dist(p,q). Maps denotes ordinary functions and Icc the "
                + "closed real interval with its usual metric. R6, R4 and Matrix4 denote "
                + "the real six-coordinate space, four-coordinate space and four-by-four matrices.")),
            Describe.Lean(
                DescribeId.Create("same-body-metric-segments"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/LengthGramMetricSegments.same_body_metric_segments"),
                H("An actual isometric interval with both exact range identifications"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Geometry/cannonfloydkenyonparry1997hyperbolic")),
                Blocks(
                    Paragraph(Text("For different endpoints let X and Y be their future unit "
                        + "Lorentz lifts. At arclength t take Gamma(t)=sinh(D-t)/sinh(D)*X "
                        + "+sinh(t)/sinh(D)*Y and project by Psi. The inverse upper-half-space "
                        + "coordinates are (x/h,y/h,(x*x+y*y+h*h-1)/(2*h), "
                        + "(x*x+y*y+h*h+1)/(2*h)). The existing sinh half-distance theorem "
                        + "gives B(lift(p),lift(q))=-cosh(dist(p,q)). Hyperbolic addition "
                        + "identities then give B(Gamma(s),Gamma(t))=-cosh(s-t). The "
                        + "interpolation has positive time, and strict monotonicity of cosh "
                        + "on nonnegative reals proves the isometry.")),
                    Paragraph(Text("For any ambient between-point z put t=dist(p,z). "
                        + "Its lift and Gamma(t) have the same pairings with X and Y. "
                        + "Their difference is Lorentz-null and orthogonal to the unit "
                        + "timelike vector X. The pinned finite-sum Cauchy-Schwarz theorem "
                        + "forces this difference to vanish. Inverse-coordinate injectivity "
                        + "therefore identifies z with the interpolated point. This proves "
                        + "full ambient rigidity, including the two endpoints.")),
                    Paragraph(Text("The original affine-segment coverage uses exactly the "
                        + "same m and f. Put r(v)=sqrt(-q(l,v)), "
                        + "a(t)=sinh(D-t)/(sinh(D)*r(lambda)), "
                        + "b(t)=sinh(t)/(sinh(D)*r(mu)), and w(t)=b(t)/(a(t)+b(t)). "
                        + "Frozen negativity makes both endpoint radii positive. Frozen "
                        + "cut_body_polytope supplies convexity through its convex-hull equality. "
                        + "Thus nu(t)=(1-w(t))*lambda+w(t)*mu lies in the original segment. "
                        + "Linearity of multiplication by m identifies its lift with a "
                        + "positive multiple of Gamma(t); both lifts have Lorentz norm -1, "
                        + "so that multiple is one. The continuous weight w runs from zero "
                        + "to one, and the intermediate value theorem supplies every original "
                        + "affine-segment point. The affine weight generally differs from "
                        + "arclength divided by D. Equal endpoints are treated separately by "
                        + "the constant map from the singleton interval.")),
                    Paragraph(Text("This is a geometric prerequisite to original section 66, "
                        + "using unchanged shared_radial_body and cut_body_polytope suppliers. "
                        + "The theorem quantifies over any witnesses of the displayed exact "
                        + "contract, so it includes irregular admissible lengths and boundary "
                        + "points. Its conditional segment statement needs no additional "
                        + "cosine assumptions once the witnesses are supplied. The original "
                        + "full-source realization domain still requires all six strict "
                        + "source cosine inequalities; the one inequality used by the frozen "
                        + "frame supplier does not establish the remaining geometry. "
                        + "No full-source realization wrapper is exported here.")),
                    Paragraph(Text("The acknowledged source supplies the classical unique-geodesic, "
                        + "Klein/hyperboloid projective, and Lorentz-distance ingredients "
                        + "(Theorem 9.3 and the discussion through page 80; Section 10, "
                        + "Theorem 10.1 on page 82 and the distance lemma on page 83). "
                        + "The exact application to the frozen cutBody and radial definitions, "
                        + "with the same m and f and both displayed range identities, is a "
                        + "repository derivation rather than a theorem stated verbatim in "
                        + "that source. No mathematical novelty claim is made. Eight actual geodesic "
                        + "halfspaces and three-dimensional interior, four triangle and four "
                        + "hexagon face incidence, prescribed original edge lengths, actual "
                        + "dihedral angles and orthogonal truncation, permutation isometries, "
                        + "inverse source realization and rigidity, volume, Schlaefli theory "
                        + "and global CFMP gluing remain separate obligations."))),
                DescribeRole.Theorem),
            Paragraph(Text("The following original APIs are used by the full plane realization. "
                + "Their statements and proof bodies remain the metric-segment owner's originals. "
                + "Phi denotes lift; Psi(Y)=((Y0+i*Y1)/(Y3-Y2),1/(Y3-Y2)). "
                + "Project is defined on B(Y,Y)=-1 and Y3>0 using the two displayed proof arguments. "
                + "R4 is the real four-coordinate space; H3 retains its hyperbolic metric. "
                + "The formula operators add, sub, mul, div, sq, neg and scale have their ordinary "
                + "real or vector meanings; tuple4 forms an ordered four-vector.")),
            Describe.Lean(
                DescribeId.Create("api-lift"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/LengthGramMetricSegments.lift"),
                H("The original Lorentz lift"), StatementSource.FromAuthor(F.Disp(LiftDefinition())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Geometry/cannonfloydkenyonparry1997hyperbolic")),
                Blocks(Paragraph(Text("This is an original consumed API of the metric-segment construction, "
                    + "used at its source by HyperbolicPlaneRealization. Its Lorentz form, lift and metric "
                    + "are unchanged."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("api-lift-unit"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/LengthGramMetricSegments.lift_unit"),
                H("Unit negative Lorentz norm"), StatementSource.FromAuthor(F.Disp(All("p", F.Id("H3"), Eq(B(Phi(F.Id("p")), Phi(F.Id("p"))), Neg(F.D(1)))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Geometry/cannonfloydkenyonparry1997hyperbolic")),
                Blocks(Paragraph(Text("This is an original consumed API of the metric-segment construction, "
                    + "used at its source by HyperbolicPlaneRealization. Its Lorentz form, lift and metric "
                    + "are unchanged."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("api-lift-cosh"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/LengthGramMetricSegments.lift_cosh"),
                H("The original actual-distance pairing"), StatementSource.FromAuthor(F.Disp(All("p", F.Id("H3"), All("q", F.Id("H3"), Eq(B(Phi(F.Id("p")), Phi(F.Id("q"))), Neg(Call("cosh", Call("dist", F.Id("p"), F.Id("q"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Geometry/cannonfloydkenyonparry1997hyperbolic")),
                Blocks(Paragraph(Text("This is an original consumed API of the metric-segment construction, "
                    + "used at its source by HyperbolicPlaneRealization. Its Lorentz form, lift and metric "
                    + "are unchanged."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("api-lift-injective"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/LengthGramMetricSegments.lift_injective"),
                H("Injectivity of the original lift"), StatementSource.FromAuthor(F.Disp(Call("Injective", F.Id("Phi")))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Geometry/cannonfloydkenyonparry1997hyperbolic")),
                Blocks(Paragraph(Text("This is an original consumed API of the metric-segment construction, "
                    + "used at its source by HyperbolicPlaneRealization. Its Lorentz form, lift and metric "
                    + "are unchanged."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("api-lift-of-coordinates"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/LengthGramMetricSegments.lift_of_coordinates"),
                H("The inverse-coordinate identity"), StatementSource.FromAuthor(F.Disp(InverseStatement())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Geometry/cannonfloydkenyonparry1997hyperbolic")),
                Blocks(Paragraph(Text("This is an original consumed API of the metric-segment construction, "
                    + "used at its source by HyperbolicPlaneRealization. Its Lorentz form, lift and metric "
                    + "are unchanged."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("api-lorentz-linear"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/LengthGramMetricSegments.lorentz_linear"),
                H("Four-term bilinear expansion"), StatementSource.FromAuthor(F.Disp(BilinearStatement())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Geometry/cannonfloydkenyonparry1997hyperbolic")),
                Blocks(Paragraph(Text("This is an original consumed API of the metric-segment construction, "
                    + "used at its source by HyperbolicPlaneRealization. Its Lorentz form, lift and metric "
                    + "are unchanged."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("api-lorentz-symm"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/LengthGramMetricSegments.lorentz_symm"),
                H("Symmetry of the original Lorentz form"), StatementSource.FromAuthor(F.Disp(All("X", F.Id("R4"), All("Y", F.Id("R4"), Eq(B(F.Id("X"), F.Id("Y")), B(F.Id("Y"), F.Id("X"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Geometry/cannonfloydkenyonparry1997hyperbolic")),
                Blocks(Paragraph(Text("This is an original consumed API of the metric-segment construction, "
                    + "used at its source by HyperbolicPlaneRealization. Its Lorentz form, lift and metric "
                    + "are unchanged."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("api-lorentz-right"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/LengthGramMetricSegments.lorentz_right"),
                H("Linearity in the second argument"), StatementSource.FromAuthor(F.Disp(RightStatement())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Geometry/cannonfloydkenyonparry1997hyperbolic")),
                Blocks(Paragraph(Text("This is an original consumed API of the metric-segment construction, "
                    + "used at its source by HyperbolicPlaneRealization. Its Lorentz form, lift and metric "
                    + "are unchanged."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("api-future-den"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/LengthGramMetricSegments.future_den"),
                H("Positive inverse-coordinate denominator"), StatementSource.FromAuthor(F.Disp(All("Y", F.Id("R4"), Implies(FutureUnit(F.Id("Y")), Lt(F.D(0), Call("sub", Coord(F.Id("Y"), 3), Coord(F.Id("Y"), 2))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Geometry/cannonfloydkenyonparry1997hyperbolic")),
                Blocks(Paragraph(Text("This is an original consumed API of the metric-segment construction, "
                    + "used at its source by HyperbolicPlaneRealization. Its Lorentz form, lift and metric "
                    + "are unchanged."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("api-project"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/LengthGramMetricSegments.project"),
                H("Projection from the future unit sheet"), StatementSource.FromAuthor(F.Disp(All("Y", F.Id("R4"), Implies(FutureUnit(F.Id("Y")), Eq(Call("coordinates", Call("project", F.Id("Y"))), Call("Psi", F.Id("Y"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Geometry/cannonfloydkenyonparry1997hyperbolic")),
                Blocks(Paragraph(Text("This is an original consumed API of the metric-segment construction, "
                    + "used at its source by HyperbolicPlaneRealization. Its Lorentz form, lift and metric "
                    + "are unchanged."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("api-lift-time"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/LengthGramMetricSegments.lift_time"),
                H("Future sheet of every original lift"), StatementSource.FromAuthor(F.Disp(All("p", F.Id("H3"), Lt(F.D(0), Coord(Phi(F.Id("p")), 3))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Geometry/cannonfloydkenyonparry1997hyperbolic")),
                Blocks(Paragraph(Text("This is an original consumed API of the metric-segment construction, "
                    + "used at its source by HyperbolicPlaneRealization. Its Lorentz form, lift and metric "
                    + "are unchanged."))), DescribeRole.Theorem))));


    private static Formula Phi(Formula p) => Call("Phi", p);
    private static Formula B(Formula x, Formula y) => Call("B", x, y);
    private static Formula Coord(Formula x, byte i) => Call("coord", x, F.D(i));
    private static Formula Neg(Formula x) => Call("neg", x);
    private static Formula Mul(Formula x, Formula y) => Call("mul", x, y);
    private static Formula Add(Formula x, Formula y) => Call("add", x, y);
    private static Formula Scale(Formula a, Formula x) => Call("scale", a, x);
    private static Formula FutureUnit(Formula y) => And(Eq(B(y,y), Neg(F.D(1))), Lt(F.D(0),Coord(y,3)));
    private static Formula LiftDefinition()
    {
        var p=F.Id("p"); var x=Call("horizontalReal",p); var y=Call("horizontalImag",p); var h=Call("height",p);
        var q=Add(Add(Call("sq",x),Call("sq",y)),Call("sq",h)); var d=Mul(F.D(2),h);
        return All("p",F.Id("H3"),Eq(Phi(p),Call("tuple4",Call("div",x,h),Call("div",y,h),
            Call("div",Call("sub",q,F.D(1)),d),Call("div",Add(q,F.D(1)),d))));
    }
    private static Formula InverseStatement()
    {
        var p=F.Id("p"); var y=F.Id("Y");
        return All("p",F.Id("H3"),All("Y",F.Id("R4"),Implies(
            And(FutureUnit(y),Eq(Call("coordinates",p),Call("Psi",y))),Eq(Phi(p),y))));
    }
    private static Formula BilinearStatement()
    {
        var x=F.Id("X"); var y=F.Id("Y"); var z=F.Id("Z"); var w=F.Id("W");
        var a=F.Id("a"); var b=F.Id("b"); var c=F.Id("c"); var d=F.Id("d");
        Formula result=Eq(B(Add(Scale(a,x),Scale(b,y)),Add(Scale(c,z),Scale(d,w))),
            Add(Add(Add(Mul(Mul(a,c),B(x,z)),Mul(Mul(a,d),B(x,w))),Mul(Mul(b,c),B(y,z))),Mul(Mul(b,d),B(y,w))));
        foreach(var name in new[]{"d","c","b","a"}) result=All(name,F.Id("R"),result);
        foreach(var name in new[]{"W","Z","Y","X"}) result=All(name,F.Id("R4"),result);
        return result;
    }
    private static Formula RightStatement()
    {
        var x=F.Id("X"); var y=F.Id("Y"); var z=F.Id("Z"); var a=F.Id("a"); var b=F.Id("b");
        Formula result=Eq(B(x,Add(Scale(a,y),Scale(b,z))),Add(Mul(a,B(x,y)),Mul(b,B(x,z))));
        foreach(var name in new[]{"b","a"}) result=All(name,F.Id("R"),result);
        foreach(var name in new[]{"Z","Y","X"}) result=All(name,F.Id("R4"),result);
        return result;
    }

    private static Formula Witness()
    {
        var l = F.Id("l"); var m = F.Id("m"); var f = F.Id("f");
        var v = F.Id("v"); var y = F.Id("y");
        return All("v", Call("C", l),
            Exists("y", F.Id("R4"), And(
                Eq(y, Call("vecMul", Call("radial", l, v), m)),
                Eq(Call("B", y, y), F.Seq(F.Minus, F.D(1))),
                Lt(F.D(0), Call("coord", y, F.D(3))),
                Eq(Call("coordinates", Call("apply", f, v)), Call("Psi", y)))));
    }

    private static Formula Statement()
    {
        var l = F.Id("l"); var m = F.Id("m"); var f = F.Id("f");
        var x = F.Id("lambda"); var y = F.Id("mu"); var gamma = F.Id("gamma");
        var c = Call("C", l); var h = F.Id("H3");
        var p = Call("apply", f, x); var q = Call("apply", f, y);
        var d = Call("dist", p, q);
        return All("l", F.Id("R6"), Implies(
            All("k", Call("Fin", F.D(6)), Lt(F.D(0), Call("coord", l, F.Id("k")))),
            All("m", F.Id("Matrix4"), All("f", Call("Maps", c, h),
                Implies(And(Call("Injective", f), Witness()),
                    All("lambda", c, All("mu", c,
                        Exists("gamma", Call("Maps", Call("Icc", F.D(0), d), h), And(
                            Call("Isometry", gamma),
                            Eq(Call("apply", gamma, F.D(0)), p),
                            Eq(Call("apply", gamma, d), q),
                            Eq(Call("range", gamma), Call("ImageSegment", l, f, x, y)),
                            Eq(Call("range", gamma), Call("Between", p, q)))))))))));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
