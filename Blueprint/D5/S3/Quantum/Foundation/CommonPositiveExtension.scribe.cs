using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class CommonPositiveExtensionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/CommonPositiveExtension.";
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula App(Formula f, params Formula[] xs) => C("apply", [f, .. xs]);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Space => V("V");
    private static Formula Cone => V("C");
    private static Formula Unit => V("u");
    private static Formula P => C("pure", Cone, Unit);
    private static Formula Dual => C("LinearMap", R, Space, R);
    private static Formula Chart(Formula p) => C("ExclusionChart", Cone, Unit, p);
    private static Formula Aff(Formula b) => C("AffineMap", R, C("EuclideanSpace", R, C("Fin", C("dim", b))), R);
    private static Formula Lift(Formula b) => C("LinearMap", R, Aff(b), Dual);
    private static Formula Res(Formula b, Formula f) => App(C("restriction", b), f);
    private static Formula Pos(Formula h) => C("ballPositive", h);
    private static Formula In(Formula x, Formula s) => Seq(x, InMacro, Sp, s);
    private static Formula Context(Formula body) => All("V", V("Type"), Seq(
        OpenBracket, C("NormedAddCommGroup", Space), CloseBracket, Sp,
        OpenBracket, C("NormedSpace", R, Space), CloseBracket, Sp,
        OpenBracket, C("FiniteDimensional", R, Space), CloseBracket, Sp,
        OpenBracket, C("Nontrivial", Space), CloseBracket, Sp,
        All("C", C("PointedCone", R, Space), All("u", Dual, body))));
    private static Formula UnderW(Formula body) => Context(Imp(C("IsClosed", Cone),
        Imp(All("x", Space, Imp(In(V("x"),Cone), Imp(Seq(V("x"),Neq,Sp,D(0)),
            Seq(D(0),F.Lt,Sp,App(Unit,V("x")))))),
        Imp(Eq(C("span",R,Cone),C("top")), Imp(C("exclusionBalls",Cone,Unit),
            Imp(C("weakPair",Cone,Unit),body))))));

    public DocumentDefinition Create()
    {
        Formula p=V("p"), a=V("a"), f=V("f"), g=V("g"), b=V("b"), h=V("h"), l=V("Lambda"), z=V("z"), x=V("x");
        Formula family=C("Function",P,Dual);
        Formula common=All("p",P,C("common",Cone,Unit,p,App(a,p)));
        Formula unique=All("p",P,All("f",Dual,Imp(C("common",Cone,Unit,p,f),Eq(f,App(a,p)))));
        Formula normal=All("p",P,All("g",Dual,Imp(C("confirms",Cone,Unit,p,g),C("ConfirmationNormalForm",a,p,g))));
        Formula laws=C("ExtensionLaws",b,App(a,p),l);
        Formula uniqueLift=Ex("Lambda",Lift(b),And(laws,All("Gamma",Lift(b),
            Imp(C("ExtensionLaws",b,App(a,p),V("Gamma")),Eq(V("Gamma"),l)))));
        Formula chartResult=All("p",P,All("b",Chart(p),And(
            C("BijOn",C("restriction",b),C("zeroPositive",Cone,Unit,p),C("positiveAffineCone",b)),uniqueLift)));
        Formula statement=UnderW(Ex("a",family,And(common,And(unique,And(normal,chartResult)))));
        Formula positiveLift=And(All("h",Aff(b),Eq(Res(b,App(l,h)),h)),
            And(All("h",Aff(b),Eq(App(App(l,h),p),D(0))),
                All("h",Aff(b),Imp(Pos(h),All("x",Space,Imp(In(x,Cone),Le(D(0),App(App(l,h),x))))))));
        Formula arcStatement=UnderW(Ex("a",family,And(common,And(unique,C("ArcFamily",a)))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The original positive restriction cone has one intrinsic linear inverse; its signed image is exactly span(Z_p).",
            H("Common positive extension on entire original exclusion balls"),Blocks(
                Paragraph(Text("Source correspondence: original VII105.4 in QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII, with only the normal-form and least clauses of VII105.3. The consumer is VIII108.5 in QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_VIII. V is the same nonzero finite dimensional real space, C the same closed generating pointed cone, u the same strictly positive original unit, K its entire normalized compact base, P all original extreme points, and proper effects the entire original interval [0,u] on ALL C. Exclusion dimensions may vary and include one. The only pair premise is weakPair on original orthogonal pairs.")),
                Describe.Lean(DescribeId.Create("zero-positive"),DeclarationHandle.Create(Owner+"zeroPositive"),
                    H("The actual original annihilating positive cone"),StatementSource.FromAuthor(Disp(
                        Context(All("p",P,All("f",Dual,new Formula.Logic(In(f,C("zeroPositive",Cone,Unit,p)),FormulaLogicOperator.Iff,
                            And(All("x",Space,Imp(In(x,Cone),Le(D(0),App(f,x)))),Eq(App(f,p),D(0))))))))),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("Z_p contains every original positive linear functional vanishing at p. It is not a selected effect subset or the whole signed annihilator of p."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("ball-positive"),DeclarationHandle.Create(Owner+"ballPositive"),
                    H("Positivity on the whole ball"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The formula notation positiveAffineCone(b) denotes the set of all h with ballPositive h. ballPositive h means 0<=h(z) for every coordinate z with norm z<=1. Since each chart is injective and its whole field identifies its image with all D_p, affine coordinate functions represent intrinsic affine functions on the entire exclusion set. The closed ball affinely spans its coordinate space."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("restriction"),DeclarationHandle.Create(Owner+"restriction"),
                    H("One linear restriction map"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("restriction b is the real-linear map f -> f.toAffineMap composed with b.param. Both its source and target include all signed functions. Only its restriction to Z_p is initially asserted injective."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("positive-lift"),DeclarationHandle.Create(Owner+"PositiveLift"),
                    H("The three extension laws"),StatementSource.FromAuthor(Disp(Context(All("p",P,All("b",Chart(p),All("Lambda",Lift(b),
                        new Formula.Logic(C("PositiveLift",b,l),FormulaLogicOperator.Iff,positiveLift))))))),AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("A real-linear map is a PositiveLift when restriction after it is the identity on every signed affine function, all its outputs vanish at p, and every nonnegative affine function has an output nonnegative on all C. These are conclusions of the construction, never premises replacing W."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("extension-laws"),DeclarationHandle.Create(Owner+"ExtensionLaws"),
                    H("Unit, inverses, order budget and intrinsic agreement"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("ExtensionLaws includes PositiveLift and Lambda(1)=u-a_p; Lambda(res f)=f for EVERY f in Z_p; 0<=Lambda h<=u-a_p on every x in C whenever 0<=h<=1 on the entire ball; range Lambda=span(Z_p). For EVERY second actual chart c and EVERY positive real-linear right inverse Gamma vanishing at p, if h and k agree whenever b.param(z)=c.param(w), with both coordinates in their closed balls, then Lambda h=Gamma k. This is intrinsic chart independence, including signed functions and charts of arbitrary admissible dimensions."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("normal-form"),DeclarationHandle.Create(Owner+"ConfirmationNormalForm"),
                    H("The paid confirmation clauses"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For every original g in F_p there are original q,r in D_p with a_p+a_q+a_r=u, g=a_p+g(q)a_q+g(r)a_r, both coefficients in [0,1], and a_p(x)<=g(x) for every x in C. The proof chooses q,r as an actual chart diameter. This is the normal form and whole-cone leastness, not the full positive or signed dual spectral expansion of VII105.3."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("whole-positive-extension"),DeclarationHandle.Create(Owner+"whole_positive_extension"),
                    H("The original positive restriction-cone theorem"),StatementSource.FromAuthor(Disp(statement)),AssessedProvenance.FromRepo(),Blocks(
                        Paragraph(Text("For arbitrary a,a' in A_p and a fixed common effect d at a cyclic companion q, completion produces c=u-a-d in A_r, then u-a'-c=d+a-a' in A_q. The reverse completion concerns the SAME triple, as proved from its singleton intersections. At every original x in C the A_q readings are nonempty and bounded in [0,u(x)]. Taking their supremum forces a(x)<=a'(x); swapping them gives equality. Since C generates V, equality holds as linear maps. This consumes the supplied joint completion and proves actual common uniqueness without assuming least effects or a frame supplier.")),
                        Paragraph(Text("A unit chart direction n gives an actual original pure q. Completion with p gives r. The public affine_zero_antipode theorem applied to 1-a_q, properness, and the completed zero readings force r to be the chart antipode. Thus a_q and a_r restrict to (1+inner(n,z))/2 and (1-inner(n,z))/2, and a_p+a_q+a_r=u on the whole V.")),
                        Paragraph(Text("For EVERY original f>=0 with f(p)=0, compactness of K gives M>0 and f<=M u on ALL C. Align a diameter with its affine restriction and put lambda=f(q), mu=f(r). The residual k=u-f/M-(1-lambda/M)a_q-(1-mu/M)a_r has k(p)=1 and vanishes on the ENTIRE D_p. Its subtracted terms are nonnegative on ALL C, hence k<=u. Directly apply the supplied whole_exclusion_support, obtaining k in A_p; uniqueness gives k=a_p. The frame sum then reconstructs f=lambda a_q+mu a_r globally. The support normalization proof is reused, not copied or counted as new extension content.")),
                        Paragraph(Text("Conversely, finite-dimensional Riesz representation aligns any affine h with one diameter. Its endpoint coefficients h(n),h(-n) are nonnegative when h is nonnegative on the whole ball. Their combination of original a_q,a_r is in Z_p and restricts to h. Reconstruction gives uniqueness of every positive fiber. This is the actual original positive restriction-cone bijection, not an assumed extension/additivity/injectivity interface.")),
                        Paragraph(Text("The nonnegative affine cone generates all signed affine functions: a sufficiently large constant shifts any affine function to nonnegative values on the compact ball. The standard mathlib ConvexCone.IsReproducing.of_span_eq_top theorem, applied in span(Z_p), expresses each element as a difference of two elements of Z_p. Positive-cone injectivity then proves restriction injective on that span, and positive lifts of two affine parts prove it surjective. The standard mathlib LinearEquiv.ofBijective constructs the inverse; inclusion into V* is the single real-linear Lambda. This establishes decomposition independence through the actual span and does not assert injectivity on every signed functional vanishing at p.")),
                        Paragraph(Text("The original u-a_p lies in Z_p and restricts to 1, giving the exact unit value. Applying positivity to h and 1-h gives the full-cone order budget. Any positive common right inverse has signed range in span(Z_p). Two chart descriptions of one intrinsic affine function therefore produce elements of that span with identical entire restrictions; injectivity proves chart independence. Applying reconstruction to u-g gives the stated confirmation normal form and whole-cone leastness."))),DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("arc-family"),DeclarationHandle.Create(Owner+"ArcFamily"),
                    H("The full all-space arc conclusion"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),Blocks(
                        Paragraph(Text("For EVERY original q,p, EVERY entire exclusion chart b of D_q, EVERY unit e with b.param(e)=p, and EVERY nonzero coordinate tangent w with inner(e,w)=0, set n=w/norm(w). There exist an original r=b.param(-e), an all-real family gamma(t)=b.param(cos(t)e+sin(t)n) of original pure points, and ONE signed linear functional B on the original V. For ALL real t, a_gamma(t)=((1+cos(t))/2)a_p+((1-cos(t))/2)a_r+sin(t)B as linear functionals on ALL V. B(p)=B(r)=0, B(b.param.linear(w))=norm(w)/2=1/(2h) for h=1/norm(w), and B vanishes on the whole span({p} union D_p). These quantifiers include every nonzero actual tangent, through the chart's injective linear direction map."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("whole-arc-effect"),DeclarationHandle.Create(Owner+"whole_arc_effect"),
                    H("The common extension's whole-space arc consumer"),StatementSource.FromAuthor(Disp(arcStatement)),AssessedProvenance.FromRepo(),Blocks(
                        Paragraph(Text("Use the SAME Lambda_q for the signed affine function H(y)=inner(n,y)/2 and define B=Lambda_q H. Every original canonical effect attached to a sphere point of D_q is in the actual Z_q. The inverse law and real linearity therefore lift the diameter identity from the whole ball to an identity on ALL V. Values at p,r and the tangent follow from restriction and the affine linear direction map.")),
                        Paragraph(Text("To prove vanishing on D_p, use the rational circle coefficients c=(1-t^2)/(1+t^2), s=2t/(1+t^2). The all-space identity and original positive effects give a_r(x)t^2+2B(x)t>=0 for every real t and every x in D_p. The standard mathlib quadratic discriminant theorem forces B(x)=0. Together with B(p)=0 this gives vanishing on M_p, without introducing a global smoothness assumption or any projection interface.")),
                        Paragraph(Text("Boundaries: full positive/signed spectral generation in VII105.3, all original positive image/kernel equalities and projection construction in VII105.5, exact VIII108.6 tangent disjointness and the VIII109 reconstruction goals remain downstream. No G, globalPair, numerical reciprocity, spectrality, PSD representation, physical implementation, or open-source claim is supplied. The construction is repository-derived; no literature novelty is claimed. The mirrored full-telescope Reg attempt has unfinished whole-family intervention/sensitivity, dependence, enrollment and sourceSelection evidence tracked in issue #29689. No declared_validated status, freeze, coverage or admission is asserted."))),DescribeRole.Theorem)
            )));
    }
}
