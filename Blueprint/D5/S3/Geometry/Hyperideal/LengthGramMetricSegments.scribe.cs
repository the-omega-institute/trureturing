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
                DescribeRole.Theorem))));

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
