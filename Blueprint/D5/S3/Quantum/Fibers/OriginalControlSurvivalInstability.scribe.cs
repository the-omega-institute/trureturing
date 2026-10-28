using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class OriginalControlSurvivalInstabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform height convergence with common scalar resource bounds need not preserve original hazard survival.",
        H("Original Control Survival Instability"), Blocks(
            Paragraph(Text("For every real c define doubleWall(c)=B(c)=(c,c,1-2c). This is the original five-mode base, with modes ordered 0,1,2,3,13 and probability vector (k,c-k,1-2c,c-k,k). The theorems use I=[0,1], duration one, 0<c<1/2, any positive natural n, and the constant real phase q(t)=phi with arbitrary real phi.")),
            Paragraph(Text("For natural n,j and real t define tent(n,j,t)=max(0,min(t-j/n,(j+1)/n-t)). For real c,t and natural n define triangle(c,n,t)=C(c,n,t)=(c/2) times the sum of tent(n,j,t) over j in the finite natural range 0<=j<n, and height(c,n,t)=c/2-C(c,n,t)/(2-t). These are total real functions with Lean's total real division; the theorems use n>=1 and t in I, where both denominators are nonzero. A finite sum retains every corner as a control value. On each closed rising half-cycle C=(c/2)(t-j/n); on each closed falling half-cycle C=(c/2)((j+1)/n-t). The predicate Legs(c,n) below denotes exactly these two universally quantified closed-leg equations for every natural j<n.")),
            Describe.Lean(DescribeId.Create("original-integral-survival"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalControlSurvivalInstability.survival"),
                H("Survival from the original derivative hazard"),
                StatementSource.FromAuthor(SurvivalDefinition()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real c, real height function k and real t, hazard(c,k,u) is max(k prime(u),0)/k(u)+max(-k prime(u),0)/(c-k(u)). The displayed integral is the real interval integral with Lebesgue measure. The definition does not assert its integrability; the construction theorem proves actual interval integrability at every endpoint t in I. Derivatives at corners are used only through almost-everywhere integral identities."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("oscillatory-original-controls"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalControlSurvivalInstability.oscillatory_original_controls"),
                H("The finite triangular family and its actual survival"),
                StatementSource.FromAuthor(ConstructionStatement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In the formula, k=height(c,n), q=constant(phi), a=c/2, m=min(c/4,1-2c), and B=B(c). OC is OriginalControl on this same base and duration one. FC is FiniteC1Control with continuous derivative rates on the closed partition pieces, and AC means AbsolutelyContinuousOnInterval on [0,1]. TV is eVariationOn on I, with real upper bounds embedded by ENNReal.ofReal. Lip(k,I,L) is LipschitzOnWith(Real.toNNReal(L),k,I). These abbreviations retain the original carrier and both regularity alternatives.")),
                    Paragraph(Text("For arbitrary real functions k,q, coordinateLength(k,q)=Length(k,q) is the real interval integral from zero to one of sqrt(k prime squared plus q prime squared), and quadraticCost(k,q)=Cost(k,q) is the same interval integral of k prime squared plus q prime squared. Both use Lebesgue measure. IL and IQ assert interval integrability of those actual integrands. II(h,0,t) asserts IntervalIntegrable(h,volume,0,t). AE(t in I,P) means that for Lebesgue-almost every real t, membership in I implies P. All remaining time quantifiers include both endpoints. The margin inequality holds for every one of the five actual probabilities.")),
                    Paragraph(Text("The partition times are j/(2n), with 2n legs. The triangle is continuous, and 2-t is at least one on I. On an open leg, differentiating the height gives -C prime/(2-t)-C/(2-t)^2. The triangle derivative is c/2 on rising legs and -c/2 on falling legs. Consequently the height derivative is -(c-k)/(2-t) on rising legs and k/(2-t) on falling legs. These rates extend continuously to each closed leg. The original finite-C1-to-AC theorem supplies absolute continuity of both coordinates.")),
                    Paragraph(Text("The bounds 0<=C<=c/(4n) and 2-t>=1 give the legal height band and uniform error bound. The signed derivative identities and that band give the speed bound 3c/4 almost everywhere. Absolute continuity and the fundamental theorem on every subinterval give the same Lipschitz bound. Its variation estimate gives TV(k)<=3c/4. Integrating the actual speed and its square gives Length<=3c/4 and Cost<=9c^2/16; measurability and domination also prove integrability of the squared derivative. The constant real phase has derivative and total variation zero.")),
                    Paragraph(Text("Substituting the signed derivatives into the original positive/negative hazard gives exactly 1/(2-t) outside the finite mesh corners. This function is continuous on I. Its primitive -log(1-t/2) gives the integral from zero to every t in I, so the integral-defined survival equals 1-t/2 at every such t. Waiting uses the same hazard definition; its derivative is zero, hence its hazard is zero and its survival is one. No prescribed survival function is an assumption of the theorem.")),
                    Paragraph(Text("These are scalar control and survival statements. They do not identify C with the instrument's actual signed-loss output, establish its variation, prove an exact identity between height total variation and length, or establish marked, quantum, operator or arbitrary-reference distance equalities. Those conclusions require their additional output and variation arguments."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-height-survival-discontinuity"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalControlSurvivalInstability.uniform_height_survival_discontinuity"),
                H("Uniform convergence with a fixed terminal discrepancy"),
                StatementSource.FromAuthor(DiscontinuityStatement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The same explicit family is used here. For every positive error tolerance there is a positive natural threshold N such that every n>=N is an original control with height error strictly below that tolerance at every point of I. Each member has the common scalar bounds proved above. Nevertheless the actual terminal survival difference from waiting is exactly one half for every n>=1, and the sequence indexed by n+1 does not converge to the waiting terminal survival.")),
                    Paragraph(Text("Choose N larger than c/(4e). The uniform estimate c/(4n) then gives convergence. The construction theorem gives survival(c,height(c,n),1)=1/2 and survival(c,constant(c/2),1)=1. Uniqueness of real limits excludes convergence of the constant terminal-survival sequence to one. Thus uniform height approximation together with these common upper resource bounds does not control scalar survival."))),
                DescribeRole.Theorem))));

    private static Formula C(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula A(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Abs(Formula a) => Seq(Bar, a, Bar);
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Interval => Seq(OpenBracket, D(0), Comma, D(1), CloseBracket);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula AllIn(string name, Formula domain, Formula body) =>
        Seq(Forall, Sp, F.Id(name), InMacro, Sp, domain, Comma, Sp, body);
    private static Formula And(params Formula[] parts)
    {
        var items = new List<Formula>();
        for (var i = 0; i < parts.Length; i++)
        {
            if (i > 0) { items.Add(Land); items.Add(Sp); }
            items.Add(Seq(Open, parts[i], Close));
        }
        return Seq([.. items]);
    }
    private static Formula SurvivalDefinition()
    {
        Formula c = F.Id("c"), k = F.Id("k"), t = F.Id("t"), u = F.Id("u");
        Formula d = A(C("deriv", k), u);
        Formula rate = Seq(Div(C("max", d, D(0)), A(k, u)), Plus,
            Div(C("max", Seq(Minus, d), D(0)), Seq(c, Minus, A(k, u))));
        return Disp(All("c", R, All("k", Seq(R, To, Sp, R), All("t", R,
            Seq(C("survival", c, k, t), Eq, Exp, Sp, Open, Minus,
                Int, Underscore, Grp(D(0)), Caret, Grp(t), Open, rate, Close,
                Sp, F.Id("d"), u, Close)))));
    }
    private static Formula ConstructionStatement()
    {
        Formula c = F.Id("c"), p = F.Id("phi"), n = F.Id("n"), t = F.Id("t"), i = F.Id("i");
        Formula k = C("height", c, n), q = C("constant", p), b = C("doubleWall", c);
        Formula a = Div(c, D(2)), margin = C("min", Div(c, D(4)), Seq(D(1), Minus, D(2), c));
        Formula speed = Div(Seq(D(3), c), D(4));
        Formula h = C("hazard", c, k), w = C("constant", a);
        Formula result = And(
            C("ValidBase", b), C("OC", b, D(1), k, q), C("FC", k, q), And(C("AC", k), C("AC", q)),
            And(Seq(A(k, D(0)), Eq, a), Seq(A(k, D(1)), Eq, a)), C("Legs", c, n),
            AllIn("t", Interval, And(Seq(Div(c, D(4)), Leq, Sp, A(k, t)), Seq(A(k, t), Leq, Sp, a),
                Seq(Abs(Seq(A(k, t), Minus, a)), Leq, Sp, Div(c, Seq(D(4), n))))),
            And(Seq(D(0), Lt, margin), AllIn("t", Interval, All("i", C("Fin", D(5)),
                Seq(margin, Leq, Sp, A(C("probability", b, A(k, t)), i))))),
            C("Lip", k, Interval, speed), Seq(C("TV", q), Eq, D(0)), Seq(C("TV", k), Leq, Sp, speed),
            All("t", R, Seq(A(C("deriv", q), t), Eq, D(0))),
            And(C("IL", k, q), C("IQ", k, q), Seq(C("Length", k, q), Leq, Sp, speed),
                Seq(C("Cost", k, q), Leq, Sp, Div(Seq(D(9), c, Caret, Grp(D(2))), D(1,6)))),
            C("AE", Seq(t, InMacro, Sp, Interval), And(Seq(A(h, t), Eq, Div(D(1), Seq(D(2), Minus, t))),
                Seq(Abs(A(C("deriv", k), t)), Leq, Sp, speed))),
            AllIn("t", Interval, And(C("II", h, D(0), t),
                Seq(C("survival", c, k, t), Eq, D(1), Minus, Div(t, D(2))))),
            C("OC", b, D(1), w, q), All("t", R, And(Seq(C("hazard", c, w, t), Eq, D(0)),
                Seq(C("survival", c, w, t), Eq, D(1)))));
        return Disp(All("c", R, All("phi", R, All("n", Nat,
            Seq(D(0), Lt, c, Lt, Div(D(1), D(2)), Land, Sp, D(1), Leq, Sp, n,
                Rightarrow, Sp, result)))));
    }
    private static Formula DiscontinuityStatement()
    {
        Formula c = F.Id("c"), p = F.Id("phi"), n = F.Id("n"), t = F.Id("t"), e = F.Id("e");
        Formula k = C("height", c, n), a = Div(c, D(2)), b = C("doubleWall", c), q = C("constant", p);
        Formula uniform = All("e", R, Seq(D(0), Lt, e, Rightarrow, Sp,
            Exists, Sp, F.Id("N"), Colon, Sp, Nat, Comma, Sp,
            D(1), Leq, Sp, F.Id("N"), Land, Sp, All("n", Nat,
                Seq(F.Id("N"), Leq, Sp, n, Rightarrow, Sp,
                    And(C("OC", b, D(1), k, q), AllIn("t", Interval,
                        Seq(Abs(Seq(A(k, t), Minus, a)), Lt, e)))))));
        Formula gap = All("n", Nat, Seq(D(1), Leq, Sp, n, Rightarrow, Sp,
            Abs(Seq(C("survival", c, k, D(1)), Minus,
                C("survival", c, C("constant", a), D(1)))), Eq, Div(D(1), D(2))));
        Formula sequence = Seq(n, Mapsto, Sp, C("survival", c, C("height", c, Seq(n, Plus, D(1))), D(1)));
        Formula nonlimit = Seq(Neg, Sp, C("Tendsto", sequence, C("atTop"),
            C("nhds", C("survival", c, C("constant", a), D(1)))));
        return Disp(All("c", R, All("phi", R, Seq(D(0), Lt, c, Lt, Div(D(1), D(2)),
            Rightarrow, Sp, And(uniform, gap, nonlimit)))));
    }
}
