using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class FiniteHorizonJointAttainmentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/FiniteHorizonJointAttainment.";

    public DocumentDefinition Create()
    {
        Formula utype = F.Id("U");
        Formula nu = F.Id("nu");
        Formula mu = F.Id("mu");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula q = F.Id("q");
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        Formula cap = F.Id("N");
        Formula policy = F.Id("p");
        Formula decode = F.Id("f");
        Formula shapes = F.Id("d");
        Formula seed = F.Id("u");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula interval = Seq(OpenBracket, D(0), Comma, D(1), CloseBracket);
        Formula booleans = F.Id("Bool");
        Formula state = F.Id("State");
        Formula policyType = Call("Policy", utype);
        Formula decoderType = Seq(state, Rightarrow, Sp, booleans);
        Formula shapeType = Seq(naturals, Rightarrow, Sp, booleans);
        Formula twoCap = Seq(D(2), cap);
        Formula oddCap = Seq(D(2), cap, Plus, D(1));
        Formula Pos(Formula x) => Seq(D(0), Lt, x);
        Formula Add(Formula x, Formula y) => Seq(Open, x, Plus, y, Close);
        Formula Sub(Formula x, Formula y) => Seq(Open, x, Minus, y, Close);
        Formula Mul(Formula x, Formula y) => Seq(x, y);
        Formula Eqn(Formula x, Formula y) => Seq(x, Eq, y);
        Formula All(Formula x, Formula type, Formula body) => Seq(
            Forall, Sp, x, Colon, type, Comma, Sp, Open, body, Close);
        Formula Ex(Formula x, Formula type, Formula body) => Seq(
            Exists, Sp, x, Colon, type, Comma, Sp, Open, body, Close);
        Formula Imp(Formula x, Formula y) => Seq(Open, x, Rightarrow, Open, y, Close, Close);
        Formula And(params Formula[] items) => Join(items, Land);
        Formula M(Formula j) => Call("moment", mu, j);
        Formula V(Formula j) => Call("coefficient", b, mu, j);
        Formula K(Formula h) => Call("minimumMean", b, mu, h);
        Formula R(Formula h) => Call("minimumRisk", b, mu, h);
        Formula J(Formula h) => Call("momentSum", mu, h);
        Formula Mean(Formula p, Formula h) => Call("cappedMean", p, nu, b, mu, h);
        Formula Joint(Formula p, Formula f, Formula h) => Call("JointAttains", p, f, nu, b, mu, h);
        Formula Min(Formula x, Formula y) => Call("min", x, y);
        Formula Correction(Formula top) => Seq(Sum, Underscore, Grp(m, Eq, D(1)),
            Caret, Grp(top), Min(D(0), V(m)));
        Formula Attainer(Formula h) => Ex(policy, policyType, Ex(decode, decoderType, Joint(policy, decode, h)));
        Formula parity = All(seed, utype, All(m, naturals,
            Imp(Seq(D(1), Leq, Sp, m), Eqn(
                Call("parity", Call("zeroReplay", policy, seed, Seq(D(2), m))),
                Seq(Open, Call("d", m), Comma, Call("d", m), Close)))));
        Formula prescribed = All(n, naturals, All(shapes, shapeType,
            Imp(Call("OptimalShapes", b, mu, n, shapes),
                Ex(policy, policyType, Ex(decode, decoderType, And(Joint(policy, decode, n), parity))))));
        Formula costLower = All(policy, policyType, All(n, naturals, Seq(K(n), Leq, Mean(policy, n))));
        Formula evenMean = Add(Sub(Mul(D(2), J(cap)), a), Mul(a, M(cap)));
        Formula oddMean = Add(Sub(Mul(D(2), J(cap)), a), Mul(Add(D(1), a), M(cap)));
        Formula costFormulas = All(cap, naturals, Imp(Seq(D(1), Leq, Sp, cap), And(
            Eqn(K(twoCap), Add(evenMean, Correction(Sub(cap, D(1))))),
            Eqn(K(oddCap), Add(oddMean, Correction(cap))))));
        Formula risk = Min(Mul(a, M(Add(cap, D(1)))), Mul(b, M(cap)));
        Formula coefficient = All(m, naturals, Imp(Seq(D(1), Leq, Sp, m), Eqn(V(m),
            Sub(Mul(b, Sub(M(Sub(m, D(1))), M(m))), Mul(a, Sub(M(m), M(Add(m, D(1)))))))));
        Formula body = Seq(Begin, Grp(F.Id("gathered")),
            Join(new[] { All(n, naturals, Attainer(n)), prescribed, costLower,
            Eqn(K(D(0)), D(0)), Eqn(K(D(1)), D(1)), costFormulas,
            Eqn(R(D(0)), Min(a, b)), All(cap, naturals, Eqn(R(oddCap), risk)),
            All(cap, naturals, Imp(Seq(D(1), Leq, Sp, cap), Eqn(R(twoCap), risk))), coefficient },
                Seq(Land, RowBreak, Grp())), End, Grp(F.Id("gathered")));
        Formula support = Call("AE", mu, Seq(Open, q, Mapsto,
            And(Pos(q), Seq(q, Lt, D(1))), Close));
        Formula statement = Disp(All(utype, F.Id("Type"),
            Imp(Call("MeasurableSpace", utype), All(nu, Call("Measure", utype),
            Imp(Call("IsProbabilityMeasure", nu), All(a, reals, All(b, interval,
            Imp(And(Pos(a), Pos(b), Eqn(Add(a, b), D(1))), All(mu, Call("Measure", interval),
            Imp(And(Call("IsProbabilityMeasure", mu), support), body))))))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite paid-prefix minima and marginal root error on one original marker source.",
            H("Finite same-source joint attainment"),
            Blocks(Describe.Lean(
                DescribeId.Create("same-source-finite-joint-attainment"),
                DeclarationHandle.Create(Prefix + "result"),
                H("One lawful history policy attains both finite endpoints"),
                StatementSource.FromAuthor(statement),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The seed space U is arbitrary and measurable, nu is its original probability law, a and b are strictly positive with a+b=1, and mu is any probability prior on the closed unit interval supported almost everywhere in its interior. The unit-interval parameter b is the original sourceLaw parameter alpha. The other root mass is a=1-b. The notation AE(mu,q maps to P(q)) means that P holds mu-almost everywhere. Each natural horizon has its own existential policy and decoder.")),
                    Paragraph(Text("The source, Policy, actualRun, zeroReplay, actualQueryCount and stoppingTime are the original AdaptiveMarkerStoppingTails objects. priorLaw is exactly the original BeneficialMarkerDeflection bind of jointLaw(nu,b,q), drawing one parameter for both arms independently of the original seed. cappedMean is the integral of actualQueryCount at the stated cap under that same priorLaw. marginalError is the real measure, under that same law, of the event that the decoder of the actualRun state differs from the original source root.")),
                    Paragraph(Text("moment(mu,j) is the integral of q to the power j against mu, and momentSum(mu,N) is the sum of these moments for indices below N. coefficient is the existing integral of (1-q)(b-aq)q to the power m-1; the final conjunct gives its exact difference-of-moments form. The displayed minimumMean formulas are K at the corresponding horizons, with an empty correction sum equal to zero. The minimumRisk formulas are the finite marginal root frontier R, including its unqueried value.")),
                    Paragraph(Text("For a positive even terminal depth 2N with N at least one, evenRisk(b,mu,N,false) is min(a M_N,b M_N), equivalently min(a,b) M_N. evenRisk(b,mu,N,true) is min(a M_(N+1),b M_(N-1)). Their minimum is R_(2N). The admissible terminal set D_N consists exactly of the Boolean shapes attaining that minimum. At an odd terminal depth the integrated error is min(a M_(N+1),b M_N), independently of the terminal parity arrangement.")),
                    Paragraph(Text("OptimalShapes(b,mu,n,d) imposes precisely two conditions. For every positive m with 2m<n, the value v_m when d(m) is true and zero otherwise equals min(0,v_m). If n is positive and even, the terminal evenRisk at N=n/2 and shape d(N) equals R_n. It imposes no other constraint. Thus every positive coefficient chooses even/even, every negative coefficient chooses odd/odd, zero coefficients allow either choice, and every d in D_N coexists with all earlier cost choices. A minimizing shape sequence exists for each horizon.")),
                    Paragraph(Text("shapePolicy always queries left from an even acquired depth. From an odd acquired depth it queries right exactly when the current right-arm parity differs from the next requested even-depth bit. Its only inputs are the original acquired action and reply lists and the original seed argument, which it ignores. The construction proves the prescribed parity at every positive even replay depth for every seed, and its lambda is exactly the requested zero-or-one bit under the original unconditioned seed law. A Unit-valued reference replay only names the deterministic action list; every original seed has that same replay and the actual law remains nu.")),
                    Paragraph(Text("The forcedRootDecoder is a measurable function of the original State. After a marker it uses the original recoveredRoot, coupled to the original source root by RawFiniteAtomLinearRealization.result, including its singleton instance. On the only leaf without a marker it compares rootEvidence for the two roots after integrating q against mu. It reads neither q nor a conditioned or additional seed. JointAttains includes integrability of the actual capped query count and means that this measurable decoder and the same lawful policy have cappedMean equal to minimumMean and marginalError equal to minimumRisk.")),
                    Paragraph(Text("The finite cost identity sums the survival tails of the actual absorbing execution. The unrestricted lower bound uses the original lambda bounds between zero and one and holds for every Policy, regardless of its error. Compact-interval finite integration and MAP comparison reuse existing measure and cylinder facts. The original-history construction realizes the whole prescribed parity sequence and is used in both coordinates of the joint endpoint. This is a repository-derived consequence of the selected stopped-mean theory; it requires no reciprocal-moment finiteness, atomic prior, assumed policy optimizer, assumed coupling or assumed MAP law."))),
                DescribeRole.Theorem))));
    }

    private static Formula Join(Formula[] items, Formula separator)
    {
        var result = new List<Formula>();
        for (var i = 0; i < items.Length; i++)
        {
            if (i != 0) result.Add(separator);
            result.Add(Seq(Open, items[i], Close));
        }
        return Seq(result.ToArray());
    }
}
