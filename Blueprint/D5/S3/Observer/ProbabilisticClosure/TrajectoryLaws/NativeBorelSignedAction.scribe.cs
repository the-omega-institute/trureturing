using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class NativeBorelSignedActionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSignedAction.";

    public DocumentDefinition Create()
    {

        Formula flow = F.Id("F"), b = F.Id("b"), k = F.Id("k"), n = F.Id("n");
        Formula f = F.Id("f"), q = F.Id("Q");
        Formula z = Call("zR", b), c = Call("cR", b), mu = Call("nuP", flow);
        Formula h = Call("late", b, Add(k, Num(4)));
        Formula d = Call("defect", b), v = Call("variation", flow, b);
        Formula phi = Call("meanDefect", flow, b);
        Formula action = Call("action", flow, f, q);
        Formula actionStatement = All(Imp(Call("Bounded", f),
            Equal(action, Times(Sub(Num(1), Call("uReal", q)),
                Call("weightedNestedIntegral", flow, f, q)))),
            ("F", "CommonFlow"), ("f", "PRealFunction"), ("Q", "PDescriptor"));
        Formula iteration = Call("meanRealIterate", flow, f, n);
        Formula iterateStatement = All(Imp(Call("Bounded", f),
            Imp(Ae(mu, q, Le(Num(0), Call("apply", f, q))),
                And(Le(Times(Pow(Fraction(Num(1), Num(5)), n), Call("mean", flow, f)), iteration),
                    Le(iteration, Times(Pow(Fraction(Num(4), Num(15)), n), Call("mean", flow, f)))))),
            ("F", "CommonFlow"), ("f", "PRealFunction"), ("n", "Nat"));
        Formula lateBound = All(Ae(mu, q,
            Le(Times(Pow(z, Add(k, Num(4))), Call("realIterate", flow, d, Num(3), q)),
                Add(Add(Times(Pow(z, Num(3)), Call("apply", h, q)),
                    Times(Pow(z, Num(2)), Call("action", flow, h, q))),
                    Times(z, Call("realIterate", flow, h, Num(2), q))))),
            ("F", "CommonFlow"), ("b", "Bool"), ("k", "Nat"));
        Formula coefficient = Add(Add(Pow(z, Num(3)), Times(Fraction(Num(4), Num(15)), Pow(z, Num(2)))),
            Times(Pow(Fraction(Num(4), Num(15)), Num(2)), z));
        Formula integrated = All(Le(Times(Times(Pow(Fraction(Num(1), Num(5)), Num(3)),
            Pow(z, Add(k, Num(4)))), phi), Times(coefficient, Call("meanLate", flow, b, Add(k, Num(4))))),
            ("F", "CommonFlow"), ("b", "Bool"), ("k", "Nat"));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Signed acquired action and the fixed three-return estimate.", H("Signed acquired action and the fixed three-return estimate"), Blocks(
                Paragraph(Text("CommonFlow contains the original two Borel probability marginals, joint flows and their Markov disintegrations, full normalized residual equations and AE complete endpoint boxes. PRealFunction means PDescriptor -> Real. Bounded(f) means measurable f with a uniform finite real norm bound. action(F,f,Q) is the Bochner integral of f against the actual weighted row F.L(Q); realIterate is its natural-number iterate. weightedNestedIntegral(F,f,Q) means integral v(W).toReal times integral f(R) dA(W) dB(Q). uReal is u.toReal. No sign restriction is placed on f in the weighted action identity.")),
                Paragraph(Text("False encodes the lower endpoint a=1/3 and true the upper endpoint b=2/5. cR is respectively 4/9 or 9/25; zR is 2/9 or 6/25; signR is +1 or -1. defect=signR(cR-g.toReal), late(j)=signR(coordinate(j,1).toReal-cR*zR^j), and variation=signR(action(F,1)-zR). mean, meanRealIterate, meanDefect and meanLate are real integrals against the original unweighted nuP. AE(mu,Q,body) binds Q almost everywhere under mu; apply denotes function application.")),
                Paragraph(Text("The public original coordinate_step and A_coordinate suppliers retain their original statements and proofs. The signed coordinate bridge converts the original ENNReal coordinate integral to a real integral after finite-measure and bounded-coordinate checks. Original unweighted marginal transport sends null inputs to null conditional rows, and L<=C then transports AE equality and order. Stationarity belongs to C=BA; L has no invariant-probability premise.")),
                Node("signed-weighted-action", "weighted_action", "The actual signed weighted action", actionStatement,
                    "Constant-density measure scaling and the Bochner kernel composition theorem identify the actual L row with (1-u)B(vAf). Boundedness provides every required integrability premise."),
                Node("signed-integrated-iterates", "integrated_iterate_bounds", "Unweighted integrated iterate comparison", iterateStatement,
                    "The actual row comparison (1/5)C<=L<=(4/15)C and the original C stationarity give one-step integral bounds. Positive action preserves marginal-AE nonnegativity; induction gives both powers on the same unweighted margin."),
                Node("signed-three-step-late", "three_step_late_bound", "The signed late predecessor controls three returns", lateBound,
                    "The original late marker ordering gives nonnegative late(j) only for j>=3. For n=k+4, positivity yields c*z^(k+3)*variation<=late(n), with variation still signed. Apply the actual action zero, one and two times. The exact identity L^3 defect=c(z^2 variation+z L variation+L^2 variation)-late(3) and late(3)>=0 give the displayed inequality with natural powers only."),
                Node("signed-integrated-three-step", "integrated_three_step", "Uniform integrated three-return estimate", integrated,
                    "Integrate the actual AE three-return inequality using bounded real functions. The lower iterate comparison is used exactly three times on defect; the upper comparison is used zero, one and two times on late(n). The resulting coefficient and (1/5)^3 do not depend on n or the Borel support."))));
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
