using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class OriginalStateCoverDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/OriginalStateCover.";
    private static Formula I(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(I(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mem(Formula a, Formula b) => F.Seq(a, F.Sp, F.InMacro, F.Sp, b);
    private static Formula Sub(Formula a, Formula b) => F.Seq(a, F.Minus, b);
    private static Formula Smul(Formula a, Formula b) => Call("smul", a, b);
    private static Formula Add(Formula a, Formula b) => F.Seq(a, F.Plus, b);
    private static Formula Mix(Formula s, Formula a, Formula b) =>
        Add(Smul(s, a), Smul(Sub(F.D(1), s), b));
    private static Formula Inst(string s, params Formula[] xs) =>
        F.Seq(F.OpenBracket, Call(s, xs), F.CloseBracket, F.Sp);
    private static Formula Conj(params Formula[] xs)
    {
        var result = xs[^1];
        for (var i = xs.Length - 2; i >= 0; i--) result = And(xs[i], result);
        return result;
    }

    private static Formula CenteredStatement()
    {
        var E = I("E"); var L = I("L"); var t = I("t"); var z = I("z");
        var f = I("f"); var w = I("w"); var real = I("Real");
        var v = Smul(F.Seq(F.Minus, t), z);
        Formula Eval(Formula a) => Call("f", a);
        var hypotheses = Conj(Call("IsCompact", L), Call("Convex", real, L),
            Mem(F.D(0), Call("interior", L)), Ex("z", E, And(Mem(z, L),
                new Formula.Relation(z, FormulaRelationOperator.NotEqual, F.D(0)))));
        var conclusion = Ex("t", real, Ex("z", E, Ex("f", Call("ContinuousLinearMaps", real, E, real),
            Conj(Lt(F.D(0), t), Mem(z, L), Mem(v, L), Lt(F.D(0), Eval(v)),
                Lt(Eval(z), F.D(0)),
                All("w", E, Imp(Mem(w, L), new Formula.Relation(Eval(z), FormulaRelationOperator.LessThanOrEqual, Eval(w)))),
                All("w", E, Imp(Mem(w, L), new Formula.Relation(Eval(w), FormulaRelationOperator.LessThanOrEqual, Eval(v))))))));
        return All("E", I("Types"), F.Seq(Inst("NormedAddCommGroup", E), Inst("NormedSpace", real, E),
            All("L", Call("Set", E), Imp(hypotheses, conclusion))));
    }

    private static Formula CoverStatement()
    {
        var V = I("V"); var C = I("C"); var u = I("u"); var real = I("Real");
        var x = I("x"); var p = I("p"); var y = I("y"); var s = I("s"); var f = I("f");
        var b = I("b"); var q = I("q"); var r = I("r"); var t = I("t");
        var K = Call("base", C, u); var P = Call("pure", C, u);
        Formula D(Formula a) => Call("exclusion", C, u, a);
        var strict = All("x", V, Imp(And(Mem(x, C),
            new Formula.Relation(x, FormulaRelationOperator.NotEqual, F.D(0))), Lt(F.D(0), Call("u", x))));
        var hypotheses = Conj(Call("IsClosed", C), strict,
            Eq(Call("span", real, C), I("top")), Call("exclusionBalls", C, u),
            Call("ExclusionInjective", C, u));
        var radial = All("b", Call("ExclusionChart", C, u, p),
            Ex("q", P, Ex("r", P, Ex("t", real,
                Conj(Mem(q, D(p)), Mem(r, D(p)), Mem(t, Call("Icc", F.D(0), F.D(1))),
                    Eq(r, Sub(Smul(F.D(2), Call("param", b, F.D(0))), q)),
                    Eq(y, Mix(t, q, r)), Eq(x, Mix(s, p, Mix(t, q, r))))))));
        var cover = All("x", V, Imp(Mem(x, K),
            Ex("p", P, Ex("y", V, Ex("s", real, Ex("f", Call("LinearMaps", real, V, real),
                Conj(Mem(y, D(p)), Mem(s, Call("Icc", F.D(0), F.D(1))), Call("proper", C, u, f),
                    Eq(Call("f", p), F.D(1)), Eq(Call("f", y), F.D(0)), Eq(x, Mix(s, p, y)),
                    Imp(Mem(x, Call("intrinsicInterior", real, K)), Mem(s, Call("Ioo", F.D(0), F.D(1)))),
                    radial)))))));
        return All("V", I("Types"), F.Seq(Inst("NormedAddCommGroup", V), Inst("NormedSpace", real, V),
            Inst("FiniteDimensional", real, V), Inst("Nontrivial", V),
            All("C", Call("PointedCone", real, V), All("u", Call("LinearMaps", real, V, real),
                Imp(hypotheses, And(Eq(K, Call("PureExclusionHullUnion", C, u)), cover))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every original state lies between a pure point and its entire exclusion ball.",
        H("Pure points, full exclusion balls and original affine diameters"),
        Blocks(
            Paragraph(Text("Let C be a closed generating cone in a nonzero finite-dimensional real normed space V, and let the original real-linear unit u be strictly positive on every nonzero element of C. Write K=C intersect {u=1}, P=ext(K), and use the entire effect interval E={f: 0<=f(c)<=u(c) for every c in C}. The set D(p) consists of every original state annihilated by some proper effect confirming the actual pure point p. Each D(p) is the image of an entire closed Euclidean unit ball under an injective affine chart, with arbitrary positive dimension depending on p. ExclusionInjective(C,u) means exactly that equality of the two entire sets D(p),D(q) implies equality of their original pure labels. PureExclusionHullUnion(C,u) denotes the union, over all p in P, of conv({p} union D(p)). The operation smul in the displayed formulas is real scalar multiplication. Pure-subtype coercions into V are implicit.")),
            Describe.Lean(DescribeId.Create("centered-affine-diameter"),
                DeclarationHandle.Create(Owner + "centered_affine_diameter"),
                H("A supporting contact of the maximal reflected body"),
                StatementSource.FromAuthor(F.Disp(CenteredStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a compact convex L containing zero in its interior and at least one nonzero point, maximize t>=0 subject to -t L being contained in L. An interior ball and a bound on the norm give a strictly positive feasible t. Testing a fixed nonzero point bounds all feasible t, and their closed conditions make the maximum attained. If every reflected point were interior, compactness would give a common neighborhood of t in which every reflected point remains interior. This would admit a larger t, a contradiction. A nonzero Hahn-Banach support at a contact v=-t z has positive maximum because zero is interior. Applying the same support inequality to -t w for every w in L makes z a global minimum of the same functional. No smoothness, strict convexity, fixed dimension or regularity of the boundary is assumed.")),
                    Paragraph(Text("This is a native proof of the classical affine-diameter existence argument, rather than a new convex-geometric existence assertion. The literature source is Barany, Hug and Schneider, Affine diameters of convex bodies, DOI 10.1090/proc12746, whose Section 5 cites Soltan's survey assertion 3.3. The result here retains the actual reflected contact and both global support inequalities needed for normalization. The proof uses compact extrema and Hahn-Banach separation from pinned Mathlib."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-state-cover"),
                DeclarationHandle.Create(Owner + "original_state_cover"),
                H("Every original state and the complete radial decomposition of its same ball"),
                StatementSource.FromAuthor(F.Disp(CoverStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The conclusion is the exact equality K=union_p conv({p} union D(p)), together with an actual decomposition for every x in the entire K. It selects an original pure p, a state y in its entire D(p), a weight s in [0,1], and one proper effect f on all V satisfying f(p)=1 and f(y)=0. For an original relative interior x that same selected weight is strictly between zero and one. For every whole-ball chart b of this same D(p), there are original pure q,r in D(p) and t in [0,1] with r=2 b(0)-q, y=t q+(1-t)r, and x=s p+(1-s)(t q+(1-t)r). Thus the radial statement concerns the same y as the first decomposition, and every positive chart dimension is retained.")),
                    Paragraph(Text("For an interior x, center K at x in the direction space of aff(K) and use the maximal reflected-body contact. Extend its support linearly to V and normalize its full minimum and maximum on K. OriginalWidthContact.normalized_effect proves that this single normalized functional is bounded between zero and u on the whole cone, not merely on the support chord. OriginalWidthContact.contact_face_subsingleton uses only the full-ball face classification and injectivity to make at least one contact face a pure singleton. Select that endpoint as p, and complement the same effect by u-f when reversing endpoints. The two possible weights are 1/(1+t) and t/(1+t).")),
                    Paragraph(Text("A pure x is represented with p=x and weight one, using any point of the nonempty D(p). A nonpure boundary x belongs to an entire D(p) by MixedExclusionGeometry.frontier_covered and uses y=x and weight zero. Convexity gives the reverse hull inclusion. Within the selected chart, a nonzero coordinate v uses n=v/||v|| and weight (1+||v||)/2; the zero coordinate uses any unit coordinate vector and equal weights. OriginalFacePolarity.chart_boundary makes both chart antipodes actual original pure states. This covers dimension one, the ball center, the sphere, pure original states, boundary states and endpoint weights.")),
                    Paragraph(Text("The assumptions contain no Pair condition, W, closed pure set, continuous pure selector, common ball center, PSD representation, fixed ambient dimension, joint completion or seed. Membership of q and r in D(p) supplies the original separate zero relations with p. The statement asserts neither distinguishability of q and r nor a three-outcome instrument. It is a mathematical consequence in the specified full-effect convex model; no physical realization or priority claim is made."))), DescribeRole.Theorem))));
}
