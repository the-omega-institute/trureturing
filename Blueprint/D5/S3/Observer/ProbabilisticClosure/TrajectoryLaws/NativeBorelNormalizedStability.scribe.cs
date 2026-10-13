using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class NativeBorelNormalizedStabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNormalizedStability.";

    public DocumentDefinition Create()
    {

        Formula flow = F.Id("F"), b = F.Id("b"), n = F.Id("n");
        Formula q = F.Id("Q"), w = F.Id("W"), x = F.Id("X");
        Formula p = F.Id("P"), r = F.Id("R"), s = F.Id("S");
        Formula z = Call("zR", b), c = Call("cR", b), d = Call("defect", b);
        Formula signEvent = All(Imp(Call("MeasurableSet", s),
            Imp(And(Call("positiveSideOrder", p, r, s), Call("negativeSideOrder", p, r, s)),
                Equal(Call("measurableTotalVariation", p, r),
                    Call("ofReal", Sub(Call("eventReal", p, s), Call("eventReal", r, s)))))),
            ("X", "CountableAtomicMeasurableSpace"), ("P", "ProbabilityMeasureX"),
            ("R", "ProbabilityMeasureX"), ("S", "SetX"));
        Formula pBound = All(Ae(Call("nuP", flow), q,
            Le(Call("fullLossP", b, q),
                Add(Add(Times(Add(Add(Num(1), z), Pow(z, Num(2))), Call("apply", d, q)),
                    Times(Add(Num(1), z), Call("action", flow, d, q))),
                    Call("realIterate", flow, d, Num(2), q)))),
            ("F", "CommonFlow"), ("b", "Bool"));
        Formula bLoss = All(Ae(Call("nuB", flow), w,
            Equal(Call("fullLossBeta", b, w),
                Add(Times(Sub(Num(1), c), Call("emissionDefectB", b, w)),
                    Times(Call("vReal", w), Call("AIntegral", flow, d, w))))),
            ("F", "CommonFlow"), ("b", "Bool"));
        Formula stability = All(Imp(Le(Num(4), n),
            Le(Call("completeLoss", flow, b), Times(Call("HR", b),
                Fraction(Call("slack", flow, b, n), Times(c, Pow(z, n)))))),
            ("F", "CommonFlow"), ("b", "Bool"), ("n", "Nat"));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Complete-configuration normalized endpoint stability.", H("Complete-configuration normalized endpoint stability"), Blocks(
                Paragraph(Text("The complete ValidTail carrier is countable and retains every finite legal word and infinity. A CountableAtomicMeasurableSpace has countably many points and measurable singletons; ProbabilityMeasureX and SetX refer to that same X. positiveSideOrder(P,R,S) means R{t}<=P{t} for every t in S; negativeSideOrder means P{t}<=R{t} for every t outside S. eventReal is the real measure of the event. Countable singleton summation compares arbitrary measurable events; probability normalization controls the reverse directed difference through the complement. Thus the sign event attains the actual full measurableTotalVariation supremum.")),
                Paragraph(Text("Ep={pAtom(0,1),pAtom(1,1),pAtom(2,1)} and Eb={betaStop,betaAtom(0,1)} are the lower-endpoint-positive events. Native marker-one mass ratios cross strictly after index two at p and after index zero at suspension. Every other finite atom has the reverse order. Native infinity mass is zero; regular_infinity_zero proves each regular descriptor also assigns it zero mass, while it remains a tested coordinate. These finite sign events evaluate the complete normalized laws and are not truncated measures.")),
                Paragraph(Text("The endpoint encoding and signed defect, late and variation are those of NativeBorelSignedAction. fullLossP and fullLossBeta are fullLoss(p,b,Q) and fullLoss(beta,b,W), where fullLoss(s,b,D) is measurableTotalVariation(law(D),native(s,endpoint(b))).toReal. completeLoss is the maximum of the two configuration loss integrals on the original marginals. meanCoordinate is integral coordinate(n,1).toReal dnuP; slack=signR(b)(meanCoordinate-cR(b)zR(b)^n). HR(false)=9839648/2657205 and HR(true)=20723912/5859375.")),
                Paragraph(Text("emissionDefectP=signR(u.toReal-r) and emissionDefectB=signR(v.toReal-r), so both equal the respective absolute emission deviations at the selected endpoint. The full residual identities give defect=(1-r)emissionDefectP+(1-u)B(emissionDefectB), which bounds each nonnegative part. AIntegral is the original A row integral and vReal=v.toReal. variation_control is the signed inequality -cR*variation <= zR*defect, equivalently the lower bound variation >= -(zR/cR)*defect; it does not give an upper bound. The separate signed_predecessor estimate cR*zR^(k+3)*variation <= late(k+4) supplies the upper bound used in the three-step argument.")),
                Node("complete-countable-sign-event", "complete_sign_event", "A full countable probability sign event", signEvent,
                    "Split any measurable event into its intersection with S and its difference from S. Countable atom comparison bounds both exchanged pieces. Normalize the probability complements to bound the reverse directed difference. Taking S itself supplies equality at the supremum."),
                Node("complete-pointwise-p-loss", "pointwise_p_loss_bound", "The full p loss before integration", pBound,
                    "Complete sign-event TV gives fullLossP=defect-late(1)-late(2). The actual first and second signed recurrences and the emission-defect bound imply the displayed pointwise AE inequality. All complete atoms participated in the sign-event comparison and normalization."),
                Node("complete-suspended-loss", "suspended_loss_formula", "The full suspended loss before integration", bLoss,
                    "Complete Eb TV, the original A_coordinate supplier, native event masses and finite real-integral conversion give the exact suspended formula. Unweighted A and B marginal transport then controls its integral on the same pair."),
                Node("uniform-normalized-stability", "normalized_stability", "Both endpoints and all return indices", stability,
                    "Let Phi be the unweighted p mean of defect and M=1+z+z^2+(1+z)(4/15)+(4/15)^2. Both complete configuration loss integrals are at most M Phi; the suspended coefficients 37/30 and 22/15 are bounded by the respective M values 3379/2025 and 9559/5625. Combine this actual complete-law conversion with integrated_three_step and integral late=slack. Positive c and z permit the final division. Exact rational evaluation gives the two stated HR values. No finite support, recurrence, deterministic successor, mixing, commutation or invariant-L premise is introduced."))));
    }

    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string prose) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Leq, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Plus, b);
    private static Formula Times(Formula a, Formula b) => Multiply(Grp(a), Grp(b));
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
    private static Formula Ae(Formula mu, Formula x, Formula body) => Call("AE", mu, x, body);
    private static Formula And(Formula a, Formula b) => Seq(Open, a, Close, Land, Open, b, Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Close, Rightarrow, Open, b, Close);
    private static Formula All(Formula body, params (string Name, string Type)[] xs)
    {
        for (var i = xs.Length - 1; i >= 0; i--)
            body = Seq(Forall, Sp, F.Id(xs[i].Name), Colon, Sp, F.Id(xs[i].Type), Comma, Sp, body);
        return body;
    }
}
