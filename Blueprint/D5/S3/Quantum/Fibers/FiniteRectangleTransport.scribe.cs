using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class FiniteRectangleTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite rectangle menu on the positive five-mode fiber has an exact continuous transport realization.",
        H("Actual Finite Rectangle Transport"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-rectangles-realize"),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/FiniteRectangleTransport.finite_rectangles_realize"),
            H("Exact realization by finite continuous controls"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The base b is the triple (X,Y,Z), with 0 < Z < 1 and 0 < X,Y < 1-Z. Its open fiber J(b) has endpoints max(0,X+Y-(1-Z)) and min(X,Y). The five probabilities, in the mode order (0,1,2,3,13), are (1-Z-X-Y+k,X-k,Z,Y-k,k). Their strict positivity and total one use the existing InteriorProbability carrier.")),
                Paragraph(Text("The direction is (1,-1,0,-1,1). The information coefficient is the sum of the four reciprocal bottom probabilities. The phase weight w is the direction divided coordinatewise by probability times information. Compatible(q(t)) asserts that the middle phase is zero and that the direction paired with the lifted phases equals the real relation phase. The state of a history q consists of the probability coordinate k, the real lifted relation phase c, and five real lifted phases v. They use the original negative phase convention psi(s)=sqrt(p(s))*exp(-i*v(s)). The instantaneous weighted phase velocity has zero probability mean, because the sum of p(s)*w(s) is zero. Duration(A) is four times the length of the finite menu A; its phase target is the sum of a times (w(k)-w(k0)) over the entries (k,a).")),
                Paragraph(Text("Admissible(b,N,q) requires continuity of the actual real-time function q, probability coordinates in J(b) on the closed interval from zero to N, finite variation of c, and an affine chart on each unit-time leg. On every open leg and for every mode, the probability derivative equals the direction times the derivative of k, and the derivative of v equals w(k) times the derivative of c. It also requires integrability of every actual transport component and equality of its integral with the corresponding terminal minus initial lifted phase. Thus the supplied object is a piecewise linear control with its transported state lift and exact integral residual.")),
                Paragraph(Text("For each menu entry, the four successive vertices change k from k0 to k, change c from zero to a at k, return k to k0, and return c to zero at k0. The phase changes on the two phase legs are a times w(k) and minus a times w(k0). Concatenating these vertices gives the real-time interpolation; matching endpoints prove continuity, and affine charts give finite variation and the differential law.")),
                Paragraph(Text("All real coefficients, including negative and zero coefficients, repeated heights, either symmetry wall, and the empty menu are included. There is no uniform speed, energy or amplitude bound. This realizes every supplied finite representation; it does not establish the existence of a representation for every vector in the full holonomy space, nor the three-height basis or the compact holonomy group."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weight-compatible"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/FiniteRectangleTransport.weight_compatible"),
                H("Middle gauge and unit relation charge"),
                StatementSource.FromAuthor(WeightStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At each interior height, the middle phase weight vanishes and the direction paired with the phase weight equals one. Strict positivity of the four bottom probabilities makes the information coefficient nonzero. These identities govern the transported gauge and relation phase on every finite rectangle and also apply pointwise to general histories."))),
                DescribeRole.Theorem),
            Paragraph(Text("Let T be finite, let k be continuous on the interval between zero and T with values in the same open fiber, and let alpha be interval integrable. Put H(i) equal to the integral of w(k(t))(i) times alpha(t), and put q equal to the integral of alpha. Each component of w composed with k is continuous: the positive affine probabilities and their positive reciprocal sum keep every denominator nonzero. Multiplication of an integrable function by a continuous function on a compact interval therefore proves that every component defining H is integrable.")),
            Paragraph(Text("Define V(b) by zero middle component, zero direction charge, equality of components 0 and 13 when X+Y=1-Z, and equality of components 1 and 3 when X=Y. Integrating the middle and charge identities gives H(2)=0 and H(0)-H(1)-H(3)+H(13)=q. On either wall the relevant affine probabilities and signs coincide, so the corresponding weights, and then their integrals, coincide. Subtracting q times w(k0), whose charge is one, shows that H-q*w(k0) belongs to V(b). This argument includes both walls simultaneously and does not require a finite affine chart decomposition.")),
            Paragraph(Text("For an absolutely continuous real phase lift chi, alpha is its derivative. The interval fundamental theorem of calculus identifies q with chi(T)-chi(0). Thus winding m gives H-2*pi*m*w(k0) in V(b), and zero winding gives H in V(b). If the five state-phase coordinates are absolutely continuous and satisfy the transport derivative law almost everywhere, the same fundamental theorem identifies H with their terminal minus initial values. Finite variation alone cannot replace absolute continuity in this endpoint statement.")),
            Paragraph(Text("For a continuous phase that is C1 on finitely many consecutive subintervals, choose arbitrary nondecreasing partition times from zero to T. On each open subinterval its derivative agrees with a continuous rate on the closed subinterval. That rate is integrable; changing values at partition endpoints does not change the interval integral. The ordinary fundamental theorem on each subinterval and telescoping of the finite endpoint sum give q=chi(T)-chi(0). Hence the same upper inclusion applies to finite piecewise C1 controls as well, without imposing unit-time legs or affine motion.")),
            Paragraph(Text("When X=Y and X+Y=1-Z, the target equations give exactly h=(t,t,0,t,t), with t any real number. The weight is ((X-k)/(2X),-k/(2X),0,-k/(2X),(X-k)/(2X)). Fix k1=k0+(upper(b)-k0)/4 before selecting t. It is an interior height distinct from k0. The real coefficient a=-2*X*t/(k1-k0) makes a*(w(k1)-w(k0)) equal h. Applying finite_rectangles_realize to the actual singleton menu [(k1,a)] supplies a continuous four-leg transport with strict support, the original gauge, zero real winding, and terminal phase h. Negative and zero targets are included. In particular the double wall has a real line of reachable residuals, including nonzero residuals.")),
            Paragraph(Text("For the construction on every stratum, put r=1-Z and A=X+Y-r. The bottom poles, in the source labels (0,1,3,13), are (A,X,Y,0). On the strict base A<X, A<Y, X>0 and Y>0. Thus the only collisions are A=0 and X=Y. Retain representatives 0 and 1, also 3 when X differs from Y, and also 13 when A differs from zero. In Fin 5 the last source label is index 4. The representative map sends 3 to 1 on X=Y and 13 to 0 on A=0, and fixes every other bottom mode. This restores both the pole and the target component in each omitted coordinate. There are g=4-deltaMinus-deltaPlus representatives, where the two indicators record the respective walls.")),
            Paragraph(Text("Fix the base and k0 before choosing the target. Enumerate the representatives by indices j from zero to g-1 and set k(j)=k0+(j/4)*(upper(b)-k0), with real division. Index zero gives k0. Since 2 <= g <= 4 and k0 is strictly below upper(b), these heights are distinct and lie strictly inside the original fiber. Every bottom probability is positive at each height, the information coefficient I is positive, and k(j) differs from every pole. Products of height differences, pole differences, and cross differences are therefore nonzero on every stratum. No genericity assumption removes either wall.")),
            Paragraph(Text("Here are explicit interpolation coefficients. For this fixed height menu define Q(t) as the product of t-k(l) over all g indices, and D(j) as the product of k(j)-k(l) over all l different from j. Let P(h) be the Lagrange polynomial of degree less than g with values h(s)*Q(lambda(s)) at the representative poles lambda(s). Equivalently P(h)(t) is the sum over representative s of h(s)*Q(lambda(s)) times the product, over representatives v different from s, of (t-lambda(v))/(lambda(s)-lambda(v)). Define a(j)=-I(k(j))*P(h)(k(j))/D(j). These are real signed coefficients determined by the target, with all heights already fixed.")),
            Paragraph(Text("The exact pinned Lagrange.interpolate, eval_interpolate_at_node, degree_interpolate_lt, eq_interpolate and interpolate_eq_sum identities give the construction without a determinant assumption. Reconstruct P(h) at the height nodes, evaluate at each representative pole, and divide by Q(lambda(s)). This yields h(s)=sum_j a(j)*w(k(j))(s). The representative map extends the equality to all bottom modes; the middle equality uses h(2)=w(k(j))(2)=0. The minus sign in a(j) comes from replacing lambda(s)-k(j) by minus (k(j)-lambda(s)) after interpolation. The probability signs have already canceled in w(s)=1/(I*(k-lambda(s))); adding another mode sign would give a different construction.")),
            Paragraph(Text("Apply weight_compatible to the reconstructed five-coordinate vector. It gives sum_j a(j)=h(0)-h(1)-h(3)+h(13). For h in V(b) this sum is zero. Consequently the reference coefficient is minus the sum of the other coefficients, and h is exactly the sum over 1 <= j < g of a(j)*(w(k(j))-w(k0)). The actual list [(k(1),a(1)),...,(k(g-1),a(g-1))] has length g-1 and all its heights are in the strict fiber. Applying finite_rectangles_realize directly to this list gives terminal phase h, zero real winding, the middle-fixed gauge and strict probabilities throughout the path. This includes the general stratum, each single wall separately, their intersection, and all signs or zeros of the coefficients.")),
            Paragraph(Text("The dimension and the rectangle count have matching quantifiers. Restriction to the representative coordinates is a linear equivalence from U(b), the space imposing the middle and wall equations, to the real functions on g representatives. Its inverse copies each representative value to its pole group and assigns zero to the middle mode. Hence U(b) has dimension g. The charge functional on U(b) is onto because w(k0) belongs to U(b) and has charge one. Rank-nullity gives dim V(b)=g-1: three off both walls, two on either single wall, and one on their intersection. On a fixed menu of n heights, the rectangle residual map is a linear map from real n-space to V(b). Surjectivity requires n >= dim V(b). The selected g-1 auxiliary heights attain this bound, and their residual differences form a basis; their coefficients are unique. This lower bound concerns a fixed target-independent menu. Individual targets can require fewer nonzero coefficients.")),
            Paragraph(Text("The finite chart description also identifies an original admissible control. On each closed unit leg, the constructed k and chi agree with affine functions whose derivatives are constant continuous rates; the transported phases obey the stated derivative law on the open leg. The complete path is continuous. The sum of its finitely many leg variations is finite, by the variation formula for adjacent intervals and the Lipschitz bound for each affine chart. It is therefore a finite piecewise C1 control with finite phase variation in the original loop class. Applying the finite piecewise fundamental theorem to every phase coordinate and using the transport derivative equality on each open leg identifies the original integral residual with the actual terminal phase. The original class also contains arbitrary absolutely continuous controls; the general-history upper inclusion above applies to those controls without a finite-chart hypothesis.")),
            Paragraph(Text("For any integer m and any target h with h-2*pi*m*w(k0) in V(b), first synthesize that remainder. Prepend the unit-time fixed-height phase leg k=k0, chi=2*pi*m*t, theta=2*pi*m*t*w(k0). Follow it by the rectangle path with its relation phase translated by 2*pi*m and its lifted phases translated by 2*pi*m*w(k0). The values match at the join, translations preserve the differential law, and weight_compatible preserves the gauge and exact real relation charge at every time. The final probability coordinate is k0, the relation phase is 2*pi*m, and the final lifted phase is h. Every integer, including negative and zero winding, is included. The phase coordinate closes on its original circle; no state or ray return is asserted.")),
            Paragraph(Math(ReachabilityStatement())),
            Paragraph(Text("Here Reachable uses the original absolutely continuous or finite piecewise C1 control class with finite phase variation and the integral of w(k)*chi', and d(b)=3-deltaMinus-deltaPlus. The necessary inclusion and the explicit list construction prove both directions. The interpolation, dimension and integration tools are classical; their application gives no mathematical priority claim. The original source's geometric-control and Cauchy-determinant references supply context, not additional hypotheses or a transport realization certificate. There is no imposed uniform speed, energy, coefficient or amplitude bound.")))));

    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Apply(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula Part(string name, Formula q, Formula t) => Call(name, Apply(q, t));

    private static Formula ReachabilityStatement()
    {
        Formula b = F.Id("b"), kzero = F.Id("kzero"), m = F.Id("m"), h = F.Id("h");
        Formula z = Seq(Mathbb, Grp(F.Id("Z")));
        Formula residual = Seq(h, Minus, D(2), Pi, Sp, m, Call("phaseWeight", b, kzero));
        return Disp(Seq(
            Forall, Sp, b, Colon, Operatorname, Grp(F.Id("Base")), Comma, Sp,
            Call("ValidBase", b), Rightarrow, Sp,
            Forall, Sp, kzero, InMacro, Call("J", b), Comma, Sp,
            Call("dim", Call("V", b)), Eq, Call("d", b), Land, Sp,
            Forall, Sp, m, InMacro, z, Comma, Sp,
            Forall, Sp, h, InMacro, Seq(R, Caret, Grp(D(5))), Comma, Sp,
            Call("Reachable", b, kzero, m, h), Leftrightarrow, Sp,
            residual, InMacro, Call("V", b)));
    }

    private static Formula WeightStatement()
    {
        Formula b = F.Id("b"), k = F.Id("k");
        Formula w = Call("phaseWeight", b, k);
        return Disp(Seq(
            Forall, Sp, b, Colon, Sp, Operatorname, Grp(F.Id("Base")), Comma, Sp,
            Call("ValidBase", b), Rightarrow, Sp,
            Forall, Sp, k, InMacro, Sp, Call("J", b), Comma, Sp,
            Apply(w, D(2)), Eq, D(0), Land, Sp,
            Apply(w, D(0)), Minus, Apply(w, D(1)), Minus,
            Apply(w, D(3)), Plus, Apply(w, D(4)), Eq, D(1)));
    }

    private static Formula Statement()
    {
        Formula b = F.Id("b"), e = F.Id("e"), menu = F.Id("A");
        Formula q = F.Id("q"), t = F.Id("t"), p = F.Id("p");
        Formula kzero = Seq(F.Id("k"), Underscore, Grp(D(0)));
        Formula duration = Call("Duration", menu);
        Formula interval = Call("J", b);
        Formula target = Call("residual", Call("phaseWeight", b), kzero, menu);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, b, Colon, Sp, Operatorname, Grp(F.Id("Base")), Comma, Sp,
            Call("ValidBase", b), Rightarrow, RowBreak, Grp(),
            Forall, Sp, kzero, InMacro, Sp, interval, Comma, Sp,
            Forall, Sp, menu, Colon, Call("List", Seq(R, Caret, Grp(D(2)))), Comma, RowBreak, Grp(),
            Open, Forall, Sp, e, InMacro, Sp, menu, Comma, Sp,
            Call("fst", e), InMacro, Sp, interval, Close, Rightarrow, RowBreak, Grp(),
            Exists, Sp, q, Colon, Seq(R, To, Sp, Operatorname, Grp(F.Id("State"))), Comma, Sp,
            Call("Admissible", b, duration, q), Land, RowBreak, Grp(),
            Apply(q, D(0)), Eq, Open, kzero, Comma, D(0), Comma, D(0), Close, Land, RowBreak, Grp(),
            Part("kappa", q, duration), Eq, kzero, Land, Sp,
            Part("chi", q, duration), Eq, D(0), Land, RowBreak, Grp(),
            Open, Forall, Sp, t, InMacro, Sp, OpenBracket, D(0), Comma, duration, CloseBracket,
            Comma, Sp, Exists, Sp, p, Colon, Call("InteriorProbability", D(4)), Comma, Sp,
            Call("weight", p), Eq, Call("probability", b, Part("kappa", q, t)), Close,
            Land, RowBreak, Grp(),
            Open, Forall, Sp, t, InMacro, Sp, OpenBracket, D(0), Comma, duration, CloseBracket,
            Comma, Sp, Call("Compatible", Apply(q, t)), Close, Land, RowBreak, Grp(),
            Part("phase", q, duration), Eq, target,
            End, Grp(F.Id("gathered"))));
    }
}
