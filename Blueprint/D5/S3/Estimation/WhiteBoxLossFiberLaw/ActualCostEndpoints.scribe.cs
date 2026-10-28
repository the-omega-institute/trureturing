using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.WhiteBoxLossFiberLaw;

internal sealed class ActualCostEndpointsDocument : IScribeDocumentDefinition
{
    private static readonly Formula R = Seq(Mathbb, Grp(F.Id("R")));
    private static readonly Formula l = LambdaLower, alpha = Alpha;
    private static readonly Formula u = F.Id("u"), v = F.Id("v"), w = F.Id("w"),
        c = F.Id("c"), d = F.Id("d"), p0 = F.Id("p0"), pA = F.Id("pA"),
        pAB = F.Id("pAB"), pB = F.Id("pB"), I = F.Id("I");
    private static Formula Flow(params Formula[] xs) => Seq(xs.SelectMany(
        (x, i) => i == 0 ? new[] { x } : new[] { Sp, x }).ToArray());
    private static Formula Call(string name, params Formula[] xs) => Flow(F.Id(name), Open,
        Flow(xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, x }).ToArray()), Close);
    private static Formula Sq(Formula x) => Seq(Grp(x), Caret, Grp(D(2)));
    private static Formula Div(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula a => Div(Pi, D(4));
    private static Formula b => Div(Pi, D(2));
    private static Formula root => Seq(Sqrt, Grp(D(2)));
    private static Formula Dalpha => Call("D", alpha);
    private static Formula J(Formula x) => Call("J", x);
    private static Formula Cost(Formula x) => Call("C", x, Dalpha);
    private static Formula Energy(Formula x, Formula code) => Call("E", x, Dalpha, code);
    private static Formula Joint => Call("V", l, alpha);
    private static Formula Child => Flow(Div(D(1), D(2)), Minus,
        Div(Sq(Flow(Call("sin", alpha), Minus, l)), D(2)));
    private static Formula Parent => Flow(l, Minus, Div(Sq(l), D(2)));
    private static Formula AB => Flow(u, Plus, v);
    private static Formula AllAngles(Formula body) => Flow(Open, Forall, alpha, InMacro, I, Comma, body, Close);
    private static Formula MinAt(Formula x) => Call("IsMinOn", F.Id("J"), I, x);
    private static Formula Attained(Formula x, Formula value) => Flow(Open,
        Exists, c, InMacro, Sq(R), Comma, c, Ge, D(0), Land, Energy(x, c), Eq, value, Land,
        Open, Forall, d, InMacro, Sq(R), Comma, d, Ge, D(0), Implies, value, Le, Energy(x, d), Close,
        Land, Cost(x), Eq, value, Close);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact nonnegative coding values give opposite endpoint slopes and interior minima on the rotating dictionary slice.",
        H("Actual Costs and Partial Absorption"),
        Blocks(
            Paragraph(Text("Let E be any real inner-product space and u,v orthogonal unit vectors. " +
                "The dictionary D(alpha) has first column u and second column cos(alpha)u+sin(alpha)v. " +
                "Set I=[pi/4,pi/2] and w=(u+v)/sqrt(2). No completeness or finite dimensionality is required. " +
                "Codes have two nonnegative real coordinates. The energy E(x,D,c) is norm(x-Dc)^2/2+lambda(c0+c1), " +
                "C(x,D) is its infimum over all such codes, and J(alpha)=pA C(u,D(alpha))+pAB C(u+v,D(alpha))+pB C(v,D(alpha)).")),
            Paragraph(Text("Write g=cos(alpha), s=sin(alpha), m=g+s-lambda, k=1-g squared, " +
                "and h=1-lambda-g m. The function activeMass(lambda,alpha) is max(0,h), and " +
                "V(lambda,alpha)=1-m squared/2-max(0,h) squared/(2k). On I the denominator k is positive. " +
                "The co-occurring sample has an optimal code a=max(0,h)/k, b=m-g a. " +
                "For every competing nonnegative code (A,B), square completion gives its energy as " +
                "1-m squared/2+(B+g A-m) squared/2+k A squared/2-h A. " +
                "If h<=0 the minimum has A=0; if h>0, completing the remaining square gives A=h/k. " +
                "The second coordinate is nonnegative in both cases, since m-g(1-lambda)=s-lambda+lambda g>0.")),
            Paragraph(Text("The child sample v has optimal code (0,s-lambda), with value 1/2-(s-lambda) squared/2. " +
                "The excess energy of (A,B) over this value is " +
                "(B+g A-(s-lambda)) squared/2+k A squared/2+(lambda+g(s-lambda))A. " +
                "Each summand is nonnegative. For the parent sample u, the existing radial alignment criterion " +
                "gives lambda-lambda squared/2. The existing nonnegative cost bounds give C(0,D)=0. " +
                "Thus these attained values concern the same infima that define J.")),
            Describe.Lean(
                DescribeId.Create("partial-absorption"),
                DeclarationHandle.Create("D5/S3/Estimation/WhiteBoxLossFiberLaw/ActualCostEndpoints.partial_absorption"),
                H("Exact slopes and every attained minimum"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For 0<lambda<1/sqrt(2), pAB>0 and pB>0, the parent weight pA may be any real number. " +
                        "The zero weight p0 is arbitrary in the expectation identity. In particular this includes all " +
                        "nonnegative normalized four-point laws on 0,u,u+v,v, including pA=0 and p0=0. " +
                        "The two existential codes in the displayed statement attain the indicated energy. Every feasible " +
                        "competing code has energy at least that attained value. Coordinatewise inequalities on real two-vectors express feasibility. " +
                "The notation N_I(x) denotes relative neighborhoods in I; H(J,q,I,x) denotes HasDerivWithinAt J q I x. " +
                "The displayed d2 is the second column; the two Lean code slots are indexed by 0 and 1.")),
                    Paragraph(Text("At pi/4 the residual h is strictly negative, so the co-occurring and child samples " +
                        "both use only the rotating column throughout a relative neighborhood. Differentiation gives the negative " +
                        "left endpoint slope. At pi/2, h=1-lambda is strictly positive. Both co-occurring coordinates are active " +
                        "throughout a relative neighborhood. Its value is 1-Q/2, where " +
                        "Q=((1-lambda) squared-2g(1-lambda)m+m squared)/(1-g squared). " +
                        "At this endpoint Q'=-2lambda(1-lambda), while the child value has derivative zero.")),
                    Paragraph(Text("The positive-part formula for V is continuous across the active-set transition, " +
                        "so J is continuous on the entire closed interval. Compactness gives an attained minimum. " +
                        "At a constrained endpoint minimum the derivative applied to every inward tangent direction is nonnegative. " +
                        "The negative slope at pi/4 and positive slope at pi/2 violate this necessary condition at their respective endpoints. " +
                        "Every interval minimizer therefore has pi/4<alpha<pi/2, placing its second atom strictly between w and v.")),
                    Paragraph(Text("This concerns exact inner coding and a dictionary slice whose first column is fixed. " +
                        "It asserts no uniqueness, continuous or monotone dependence on probability ratios, optimum when both columns " +
                        "are free, decoder bias result, amortized encoder result or empirical sparse autoencoder result. " +
                        "The classical radial cost is reused; the endpoint calculation and its attained two-coordinate value relation " +
                        "are stated here without a claim of literature novelty."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula geom = Flow(Forall, F.Id("E"), InMacro, F.Id("RealInnerProductSpaces"), Comma,
            Forall, u, Comma, v, InMacro, F.Id("E"), Comma, Open,
            Call("norm", u), Eq, D(1), Land, Call("norm", v), Eq, D(1), Land,
            Langle, u, Comma, v, Rangle, Eq, D(0), Close, Implies);
        Formula qA = Flow(Minus, Div(Flow(pB, Open, Div(D(1), root), Minus, l, Close), root));
        Formula qB = Flow(pAB, l, Open, D(1), Minus, l, Close);
        Formula expectation = AllAngles(Flow(Forall, p0, InMacro, R, Comma,
            p0, Cost(D(0)), Plus, pA, Cost(u), Plus, pAB, Cost(AB), Plus, pB, Cost(v), Eq, J(alpha)));
        Formula attained = AllAngles(Flow(Cost(u), Eq, Parent, Land,
            Attained(AB, Joint), Land, Attained(v, Child)));
        Formula neighborhoods = Flow(
            Call("Eventually", Call("N", I, a),
                Flow(alpha, Mapsto, Call("DifferentiableWithinAt", R, F.Id("J"), I, alpha))), Land,
            Call("Eventually", Call("N", I, b),
                Flow(alpha, Mapsto, Call("DifferentiableWithinAt", R, F.Id("J"), I, alpha))));
        return Disp(Flow(geom,
            Forall, l, Comma, pA, Comma, pAB, Comma, pB, InMacro, R, Comma,
            Open, D(0), Lt, l, Lt, Div(D(1), root), Land, D(0), Lt, pAB, Land, D(0), Lt, pB, Close,
            Implies, Esc,
            Call("d2", a), Eq, w, Land, Call("d2", b), Eq, v, Land, expectation, Land, attained, Land,
            Call("ContinuousOn", F.Id("J"), I), Land, neighborhoods, Land,
            Call("H", F.Id("J"), qA, I, a), Land, Call("H", F.Id("J"), qB, I, b), Land,
            qA, Lt, D(0), Land, D(0), Lt, qB, Land,
            Open, Exists, alpha, InMacro, I, Comma, MinAt(alpha), Close, Land,
            AllAngles(Flow(MinAt(alpha), Implies, a, Lt, alpha, Lt, b))));
    }
}
