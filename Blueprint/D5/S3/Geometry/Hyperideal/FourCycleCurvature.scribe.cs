using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FourCycleCurvatureDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/FourCycleCurvature.fourcycle_curvature_box";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual occurrence-counted curvature has a uniform inward margin on an explicit global four-cycle box.",
        H("From local angle envelopes to all global curvature faces"),
        Blocks(
            Paragraph(Text("T is an arbitrary finite type of tetrahedra. E is an arbitrary "
                + "global-edge type with decidable equality. "
                + "An incidence s has edge:T -> Fin(6) -> E and low:E -> Bool. In the local "
                + "order (12,13,14,34,24,23), slots 0 and 3 are high and the other four are low. "
                + "FourCycle(s) requires this equality at every local slot, degree eight for "
                + "every low global label, and degree at least twelve for every high label. "
                + "Degree is the actual cardinality of the fibre of edge, including repeated labels.")),
            Paragraph(Text("For each local target, frame is an explicit permutation induced by "
                + "a tetrahedral vertex relabeling. Its zeroth coordinate is the target; for "
                + "a low target its slots 0,1,3,4 are low. All frame coordinates read the SAME "
                + "global vector x:E -> Real. C(s,x,o) is the previous exact six-variable cosine "
                + "after this relabeling. The angle is arccos(C), and K(s,x,e) is 2pi minus "
                + "the sum over all occurrences o with source e.")),
            Paragraph(Text("Set m=card(T x Fin(6)), t=pi/(m+2), c=cos(t), and "
                + "delta(T)=min(1/8,(1-c)/(2+c)). The lower vector L(s) has value 5/4 "
                + "at low labels and 1+delta at high labels. U(s) has value 2 at low labels "
                + "and 8/5 at high labels. Box(s,x) means L(s)(e)<=x(e)<=U(s)(e) for all e. "
                + "The size-independent eta is min(pi, min(2pi-8arccos(293/400), "
                + "min(8arccos(1577/2236)-2pi,12arccos(37/43)-2pi))).")),
            Paragraph(Text("Application: the actual degree-normalized forward flow on a supplied genuine box. Let C be any compact "
                + "set of six-length vectors, each with six positive coordinates and all six original source cosines "
                + "strictly between -1 and 1. There are constants 0<mu<=M, with M>0, depending only on C. These constants "
                + "are chosen before the arbitrary finite tetrahedron type T, finite edge type E, decidable edge equality, "
                + "incidence s and global length box below. The original six local slots and arccos branches are retained.")),
            Paragraph(Text("For a nonempty box B=[a,b] in E->Real, require every p in B to have positive coordinates and every local "
                + "read R_t(p)=(p(s.edge(t,q)))_q to belong to C. Put d_e=degree(s,e) and K_e(p)=curvature(s,cosh(p),e), "
                + "the original occurrence-counted curvature. Assume K_e(p)>0 on every lower face p_e=a_e and K_e(p)<0 on "
                + "every upper face p_e=b_e. Fix c in B with K(c)=0. These are the hypotheses of this application; the "
                + "supplied zero is retained.")),
            Paragraph(Text("Let J_t(p) be the actual six-angle derivative at R_t(p). Full-domain positive definiteness from the "
                + "LengthGramBody angle application and compactness of C give mu*sum_q(v_q^2)<=v dot "
                + "J_t(p)v<=M*sum_q(v_q^2). The actual curvature differential satisfies -v dot DK_p[w]=sum_t R_t(v) dot "
                + "J_t(p)R_t(w). Counting the full occurrence fibers gives sum_t sum_q(R_t(v)_q^2)=sum_e d_e*v_e^2, "
                + "including repeated global labels within a tetrahedron. Hence the negative curvature derivative is "
                + "symmetric, with these degree-weighted lower and upper bounds.")),
            Paragraph(Text("Integrate the lower derivative bound along the straight segment from x to y in the same box. It gives "
                + "mu*sum_e d_e*(y_e-x_e)^2<=-sum_e(K_e(y)-K_e(x))*(y_e-x_e). The zero-curvature equation at c forces every "
                + "d_e>0. Weighted Cauchy-Schwarz then gives mu*sqrt(sum_e d_e*(p_e-c_e)^2)<=sqrt(sum_e K_e(p)^2/d_e) for "
                + "every p in B. In particular K(p)=0 implies p=c within this box.")),
            Paragraph(Text("Every initial x0 in B has a forward trajectory n with n(0)=x0, n(t) in B and n'_e(t)=K_e(n(t))/d_e for "
                + "all t>=0, including the derivative at zero. To obtain a global solution, clamp coordinates to [a,b] and "
                + "compose the actual normalized field with this clamp. Its derivative is bounded on the compact box, so "
                + "the clamped field is globally Lipschitz and bounded. Picard-Lindelof supplies a uniform local time "
                + "interval and the existing uniform local-to-global pasting theorem supplies a global clamped solution. "
                + "The strict inward signs keep its nonnegative-time trajectory inside the same box, where the clamped and "
                + "original fields agree.")),
            Paragraph(Text("For W(t)=sum_e d_e*(n_e(t)-c_e)^2 the actual differential equation and the preceding two-point "
                + "inequality give W'(t)<=-2*mu*W(t). Pinned Mathlib Gronwall therefore yields "
                + "sqrt(W(t))<=exp(-mu*t)*sqrt(W(0)) for every t>=0. This is the degree-weighted distance to the supplied "
                + "equilibrium along the actual normalized flow, with the original time variable. It includes zero initial "
                + "error and repeated local occurrences.")),
            Paragraph(Text("This application combines the original angle derivative, finite incidence sums, compact derivative "
                + "bounds, box invariance, Picard-Lindelof, uniform local-to-global pasting and scalar Gronwall. It proves "
                + "the stated conditional trajectory, residual estimate and uniqueness of a zero in the supplied box. "
                + "Constructing the box and equilibrium from a particular geometric entrance, physical Schlaefli and "
                + "co-volume identification, and conclusions outside the supplied box remain separate obligations. The "
                + "application adds no mathematical declaration or novelty claim.")),
            Paragraph(Text("For FourCycle incidence data, the existing cosh-coordinate entrances are "),
                Ref("D5/S3/Geometry/Hyperideal/FourCycleCurvature.fourcycle_curvature_box"),
                Text(" and "),
                Ref("D5/S3/Geometry/Hyperideal/FourCycleExistence.fourcycle_zero_curvature"),
                Text(". The flow application above instead takes its box, compact local family and equilibrium "
                    + "in actual length coordinates. Their concrete composition requires the coordinatewise "
                    + "arcosh correspondence with the same global labels and occurrence fibers.")),
            Describe.Lean(
                DescribeId.Create("fourcycle-global-curvature-box"),
                DeclarationHandle.Create(Declaration),
                H("An explicit nonempty box with signed margin on every face"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The derivative-based local theorem is consumed directly. "
                        + "The proof checks the actual finite frame permutations, proves the "
                        + "trigonometric gaps from exact square-root comparisons, and constructs "
                        + "delta rather than assuming an unspecified sufficiently small number. "
                        + "It proves cos(t)<2(1-delta)/(2+delta), so on a high lower face each "
                        + "angle is below t. There are at most m occurrences at any edge; hence "
                        + "the angle sum is below pi and its curvature exceeds pi.")),
                    Paragraph(Text("On low lower and upper faces the exact cardinality is eight. "
                        + "The corresponding arccos bounds are summed over the actual fibre. "
                        + "On a high upper face the cardinality is at least twelve and all "
                        + "arccos values are nonnegative. These give the three fixed gaps in eta. "
                        + "The same proof shows -1<C(s,x,o)<1 throughout the box, and the lower "
                        + "vector itself witnesses nonemptiness. No solution or face sign is assumed.")),
                    Paragraph(Text("This is a real incidence-system theorem. The formal statement "
                        + "does not certify that the incidence system is a manifold, prove the "
                        + "hyperbolic realization of each angle formula, or invoke an unproved "
                        + "Brouwer or co-volume existence axiom. Those geometric identifications "
                        + "and the ordinary variational existence step remain separate."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var s=F.Id("s"); var x=F.Id("x"); var e=F.Id("e"); var o=F.Id("o");
        var delta=Call("delta",F.Id("T")); var eta=F.Id("eta");
        var lower=Call("L",s); var upper=Call("U",s);
        var c=Call("C",s,x,o); var k=Call("K",s,x,e);
        var nondeg=All([("o",Call("Product",F.Id("T"),Call("Fin",F.D(6))))],
            And(Lt(F.Seq(F.Minus,F.D(1)),c),Lt(c,F.D(1))));
        var faces=All([("e",F.Id("E"))],And(
            Imp(Eq(Apply(x,e),Apply(lower,e)),Le(eta,k)),
            Imp(Eq(Apply(x,e),Apply(upper,e)),Le(k,F.Seq(F.Minus,eta)))));
        var conclusion=And(Lt(F.D(0),delta),Le(delta,Rat(1,8)),Lt(F.D(0),eta),
            Call("Box",s,lower),All([("x",new Formula.TypeArrow(F.Id("E"),F.Id("Real")))],
                Imp(Call("Box",s,x),And(nondeg,faces))));
        return All([("T",F.Id("Type")),("E",F.Id("Type")),
            ("s",Call("Incidence",F.Id("T"),F.Id("E")))],
            Imp(And(Call("Fintype",F.Id("T")),Call("DecidableEq",F.Id("E")),
                Call("FourCycle",s)),conclusion));
    }

    private static Formula All((string Name,Formula Type)[] variables,Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(v=>new Formula.BoundVariable(FormulaIdentifier.Create(v.Name),v.Type))],body);
    private static Formula And(params Formula[] p)
    {
        if(p.Length==0) throw new ArgumentException("Empty conjunction");
        var q=p[^1]; for(var i=p.Length-2;i>=0;i--) q=new Formula.Logic(p[i],FormulaLogicOperator.And,q);
        return q;
    }
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Apply(Formula function,params Formula[] args)=>
        new Formula.Apply(function,[..args]);
    private static Formula Rat(int n,int d)=>F.Seq(F.Frac,F.Grp(Number(n)),F.Grp(Number(d)));
    private static Formula Number(int value) => value switch
    {
        1 => F.D(1), 8 => F.D(8),
        _ => throw new ArgumentOutOfRangeException(nameof(value)),
    };
    private static Formula Call(string name,params Formula[] args)
        => Apply(F.Id(name),args);
}
