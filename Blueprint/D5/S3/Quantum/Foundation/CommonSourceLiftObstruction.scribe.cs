using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class CommonSourceLiftObstructionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.";
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula App(Formula f, params Formula[] xs) => C("apply", [f, .. xs]);
    private static Formula In(Formula x, Formula s) => Seq(x, InMacro, Sp, s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula Dual => C("LinearMap", R, V("V"), R);
    private static Formula P => C("pure", V("C"), V("u"));
    private static Formula Fn(Formula s, Formula t) => C("Function", s, t);
    private static Formula Dp(Formula p) => C("exclusion", V("C"), V("u"), p);
    private static Formula Pos(Formula b) => All("z", V("V"), Imp(In(V("z"), V("C")), Le(D(0), App(b, V("z")))));
    private static Formula B(Formula b) => C("baseMaximum", V("C"), V("u"), b);
    private static Formula Norm(Formula b) => C("stateNorm", V("C"), V("u"), b);
    private static Formula Alpha(Formula p, Formula t) => C("upperDisplacement", p, t);
    private static Formula Normal(Formula b) => C("normalizePositive", V("C"), V("u"), b);
    private static Formula Distance(Formula p, Formula t, Formula h) => C("sourceDistance", V("C"), V("u"), p, t, h);
    private static Formula Limit(Formula f, Formula x) => C("Tendsto", f, C("atTop"), C("nhds", x));
    private static Formula Uniform(Formula f, Formula ell) => C("TendstoUniformly", f, ell, C("atTop"));
    private static Formula Proper(Formula b) => C("proper", V("C"), V("u"), b);
    private static Formula Fin(Formula m) => C("Fin", m);
    private static Formula Dim(Formula t) => C("affdim", Dp(t));
    private static Formula DiffNorm(Formula x, Formula y) => C("norm", C("sub", x, y));
    private static Formula Context(Formula body) => All("V", V("Type"), Seq(
        OpenBracket, C("NormedAddCommGroup", V("V")), CloseBracket, Sp,
        OpenBracket, C("NormedSpace", R, V("V")), CloseBracket, Sp,
        OpenBracket, C("FiniteDimensional", R, V("V")), CloseBracket, Sp,
        All("C", C("PointedCone", R, V("V")), All("u", Dual,
        Imp(C("IsClosed", V("C")),
        Imp(All("z", V("V"), Imp(In(V("z"), V("C")), Imp(Seq(V("z"), Neq, Sp, D(0)), Lt(D(0), App(V("u"), V("z")))))),
        Imp(Eq(C("span", R, V("C")), C("top")), Imp(C("exclusionBalls", V("C"), V("u")), body))))))));
    private static Formula Local(Formula body) => Context(All("p", P, Imp(C("SingleLabel", V("C"), V("u"), V("p")),
        All("y", V("V"), Imp(In(V("y"), C("intrinsicInterior", R, Dp(V("p")))), body)))));

    public DocumentDefinition Create()
    {
        Formula p=V("p"), t=V("t"), b=V("b"), a=V("a"), h=V("h"), m=V("m"), i=V("i"), n=V("n"), ell=V("ell"), eps=V("epsilon"), delta=V("delta"), tau=V("tau"), y=V("y"), r=V("r"), A=V("A");
        Formula controlBound = Le(B(b), C("div", C("faceMaximum",p,b),
            C("sub",D(1),C("mul",A,Alpha(p,t)))));
        controlBound = All("t",P,Imp(Lt(C("mul",A,Alpha(p,t)),D(1)),
            All("b",Dual,Imp(Pos(b),Imp(Eq(App(b,t),D(0)),controlBound)))));
        Formula control = And(Lt(D(0),A),And(
            All("b",Dual,Le(C("dualNorm",b),C("mul",A,Norm(b)))),And(
            C("Tendsto",C("upperDisplacementAt",p),C("nhds",p),C("nhds",D(0))),controlBound)));
        control = Context(All("p",P,Ex("A",R,control)));
        Formula bn=App(b,n), tn=App(t,n), fn=Normal(bn);
        Formula normalization = And(All("n",N,And(Proper(fn),Eq(App(fn,tn),D(0)))),And(
            Limit(C("normalizationGaps",V("C"),V("u"),b),D(0)),And(
            Uniform(C("normalizedRestrictions",p,b),ell),
            Imp(Eq(C("sSup",C("range",ell)),D(1)),
                Limit(C("baseMaxima",V("C"),V("u"),b),D(1))))));
        normalization = Imp(Uniform(C("restrictions",p,b),ell),normalization);
        normalization = All("ell",Fn(Dp(p),R),Imp(
            All("x",Dp(p),And(Le(D(0),App(ell,V("x"))),Le(App(ell,V("x")),D(1)))),normalization));
        normalization = Imp(All("n",N,Eq(App(bn,tn),D(0))),normalization);
        normalization = Imp(All("n",N,Pos(bn)),normalization);
        normalization = Context(All("p",P,All("t",Fn(N,P),Imp(Limit(t,p),All("b",Fn(N,Dual),normalization)))));
        Formula shrinking = All("x",V("V"),Imp(In(V("x"),Dp(App(r,n))),Lt(DiffNorm(V("x"),p),eps)));
        shrinking = Ex("j",N,All("n",N,Imp(Le(V("j"),n),shrinking)));
        shrinking = Local(All("r",Fn(N,P),Imp(Limit(C("values",r),y),
            All("epsilon",R,Imp(Lt(D(0),eps),shrinking)))));
        Formula nearby = Or(Le(C("add",Dim(p),D(1)),Dim(t)),
            Ex("i",Fin(m),Le(delta,Distance(p,t,App(h,i)))));
        nearby = All("r",P,Imp(Lt(DiffNorm(r,y),eps),All("t",P,Imp(In(t,Dp(r)),nearby))));
        Formula vanish = All("r",P,Imp(Lt(DiffNorm(r,y),eps),All("t",P,Imp(In(t,Dp(r)),
            All("i",Fin(m),Le(App(App(h,i),t),tau))))));
        vanish = All("tau",R,Imp(Lt(D(0),tau),Ex("epsilon",R,And(Lt(D(0),eps),vanish))));
        Formula family = All("i",Fin(m),And(In(App(a,i),Dp(p)),
            In(App(h,i),C("fullZeroConfirmers",V("C"),V("u"),App(a,i)))));
        Formula obstruction = And(family,And(
            Ex("epsilon",R,Ex("delta",R,And(Lt(D(0),eps),And(Lt(D(0),delta),nearby)))),vanish));
        obstruction = Local(Ex("m",N,And(Lt(D(0),m),
            Ex("a",Fn(Fin(m),P),Ex("h",Fn(Fin(m),Dual),obstruction)))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite common source tests force an original positive-lift error or an increase of the return ball's intrinsic affine dimension.",
            H("Finite common source tests on the whole original positive cone"), Blocks(
            Paragraph(Text("The source is QUANTUM_ORIGIN_LOCAL_PURE_LIMIT_AND_COMMON_POSITIVE_LIFTS_CONTINUATION, 132.1--132.4. V is an arbitrary finite dimensional real normed space; C is the entire closed generating pointed cone; u is strictly positive on its nonzero vectors. K is its whole normalized base, P all original extreme points, and effects the complete interval [0,u] on C. Every entire original exclusion D(t) is a positive dimensional affine Euclidean closed ball; dimensions may vary and segments are included. All distances and dual norms use the supplied original norm. No global injectivity, fixed dimension, closedness of P, common inner product or continuous choice of charts is assumed.")),
            Describe.Lean(DescribeId.Create("base-maximum"),DeclarationHandle.Create(Owner+"baseMaximum"),H("Maximum on the whole original K"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("baseMaximum(b)=sup b(K); compactness gives the actual maximum. For positive b it is exactly the supremum norm of the original stateReadout on all K."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("upper-displacement"),DeclarationHandle.Create(Owner+"upperDisplacement"),H("Whole-ball upper displacement"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("upperDisplacement(p,t)=max over x in the entire D(t) of infDist(x,D(p)). The notation upperDisplacementAt(p) in the formula means t mapped to this number."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("source-readout"),DeclarationHandle.Create(Owner+"sourceReadout"),H("Restriction to all of F"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("sourceReadout(p,b) is the continuous real function x mapped to b(x) on all F=D(p). Its supremum norm is a seminorm on ambient linear functionals. No quotient identifying different original states is imposed."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("normalize-positive"),DeclarationHandle.Create(Owner+"normalizePositive"),H("The original global unit normalization"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("normalizePositive(b)=b/max(1,baseMaximum(b)), using scalar multiplication on the original dual space and the entire original state body."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("source-distance"),DeclarationHandle.Create(Owner+"sourceDistance"),H("Distance to the entire positive zero cone"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("sourceDistance(p,t,h)=inf over every b positive on ALL C and exactly zero at this SAME t of max over x in ALL F of abs(b(x)-h(x)). It is infDist from sourceReadout(p,h) to the restriction image of CommonPositiveExtension.zeroPositive(C,u,t) in C(F,R). Zero makes this image nonempty. It need not be closed; no attainment is assumed. There is no b<=u restriction and no pointwise or label-dependent patchwork."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("moving-positive-control"),DeclarationHandle.Create(Owner+"moving_positive_control"),H("132.2: all moving positive annihilators share one control"),StatementSource.FromAuthor(Disp(control)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("One A>0 bounds the supplied original dual norm by A times the whole-K norm for EVERY signed linear b. The entire compact K spans V, so its restriction map is injective and the pinned finite dimensional antilipschitz theorem supplies A. Pure-label upper incidence gives alpha(p,t)->0 at p, with no singleton-label premise. For every t with A alpha(p,t)<1 and EVERY positive b with b(t)=0, max_K b <= max_F b/(1-A alpha(p,t)). The existing positive_annihilator_maximum places a global maximum in D(t). Its nearest point in the same F and the dual estimate give the inequality; the zero functional is included."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("moving-positive-normalization"),DeclarationHandle.Create(Owner+"moving_positive_normalization"),H("132.2: normalize every unbounded positive sequence"),StatementSource.FromAuthor(Disp(normalization)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("For every original pure t(n)->p and every b(n) positive on all C and zero at t(n), suppose restrictions to all F converge uniformly to any ell:F->[0,1]. Continuity of ell is derived. With B(n)=max_K b(n), f(n)=b(n)/max(1,B(n)), every f(n) is an original proper effect, f(n)(t(n))=0, the whole-K norm of f(n)-b(n) tends to zero, and restrictions f(n)|F converge uniformly to the same ell. If sup_F ell=1, B(n)->1. The proof in fact sandwiches B(n) to the supremum norm of ell. In the formula, restrictions, normalizedRestrictions, normalizationGaps and baseMaxima denote these exact sequences, and values denotes subtype coercion into V. No bound on b(n), unit budget, singleton assumption or moving chart continuity is inserted."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("single-label-mixed-shrinking"),DeclarationHandle.Create(Owner+"single_label_mixed_shrinking"),H("132.3: entire exclusions shrink to the local label"),StatementSource.FromAuthor(Disp(shrinking)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("Assume only I(F)={p}, expressed by SingleLabel(C,u,p), and y in the relative interior of F. Any hypothetical original pure sequence r(n)->y forces EVERY mixed x in D(r(n)) eventually within each positive epsilon of p. Complete common confirmers and compactness of the entire effect interval give one limiting effect equal to one on all F. Two distinct actual pure sphere points in F have different complete exclusions by single_label_neighbor, including dimension one. Two-point face rigidity then forces every exclusion cluster point to be p. Compactness upgrades this to uniform shrinking of the entire fibers. No injectivity criterion is applied to the mixed y and no such pure sequence is asserted to exist."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-common-source-obstruction"),DeclarationHandle.Create(Owner+"finite_common_source_obstruction"),H("132.4: positive source error or intrinsic dimension increase"),StatementSource.FromAuthor(Disp(obstruction)),AssessedProvenance.FromRepo(),Blocks(
                Paragraph(Text("There are m>0 actual pure a(i) in F and fixed complete original h(i) in A(a(i)), chosen before ALL original r,t, and epsilon,delta>0. For every pure r with original norm distance to y less than epsilon and every pure t in the entire D(r), either affdim D(t)>=affdim F+1 or some sourceDistance(p,t,h(i))>=delta. Since Fin m is finite and nonempty, this last clause is exactly max_i R_F(t,h(i))>=delta. affdim means the real finrank of the direction of the actual affine span, not a chart certificate. For EVERY tau>0 a possibly different positive epsilon gives ALL h(i)(t)<=tau simultaneously for every such r,t, with the same finite family, source F and return t.")),
                Paragraph(Text("A finite simplex around the coordinate of y fits in the open ball. Each simplex vertex belongs to the convex hull of the entire sphere, so finite sphere subsets give a finite actual pure family spanning F with y in the relative interior of its convex hull. Local singleton propagation applies to every a(i). Any chosen full zero confirmer has whole original one-face exactly {a(i)}: proper face maximality identifies every pure one-point, and the compact exposed top face is the closed convex hull of its extreme points. Original zero symmetry gives h(i)(p)=0.")),
                Paragraph(Text("A failure of the uniform obstruction produces a SAME r(n),t(n) for all tests with r(n)->y, t(n) in D(r(n)), actual affdim D(t(n))<=k, and every source distance tending to zero. Selection from the infimum gives positive b(i,n) zero at this same t(n) with uniform whole-F error tending to zero, without minimizers. The entire-fiber shrinking gives t(n)->p. Moving positive normalization yields proper f(i,n) with the same source limits. Original pure maxima lie in the SAME entire D(t(n)); compact joint limits of effects and states, upper incidence, and the singleton whole one-face force x(i,n)->a(i).")),
                Paragraph(Text("Extract one subsequence of constant positive integer dimension d<=k. Compactness of K gives a whole-ball Hausdorff limit H and the ORIGINAL parameter_subsequence theorem gives a further common convergent center and linear map, with H=c+L(closed unit ball). Upper incidence gives H subset F. Every finite a(i) lies in H; therefore affineSpan H=affineSpan F and rank L=k. Since rank L<=d<=k, d=k and L is injective. ONLY NOW the existing affine_ball_boundary_limit theorem transports the pure r(n), which lie on those same return spheres, to the relative boundary of H. The finite convex hull lies in H and has that same affine span, so y is also in the relative interior of H, a contradiction. No boundary claim is made for a rank-collapsed map. Centers and arbitrary chart maps are controlled through their entire images, so no common axes or continuous chart choices are assumed.")),
                Paragraph(Text("132.5 remains a boundary: this proves neither LP(p,y), existence of an original pure sequence approaching the mixed y, existence of common positive lifts, resolution of repeated balls, nor a complete EB countermodel. A maximal dimension F removes only the dimension-increase branch; no arbitrary specified F is replaced by a maximal one, and the source-error branch remains. Separate return labels for separate tests do not meet the same-label requirement. The whole-K effect-distance obstruction with global injectivity and fixed dimension is not used as a bridge to this stronger source-F positive-cone distance. The result is repository-derived, with no global originality or physical-realization claim."))),DescribeRole.Theorem)
            )));
    }
}
