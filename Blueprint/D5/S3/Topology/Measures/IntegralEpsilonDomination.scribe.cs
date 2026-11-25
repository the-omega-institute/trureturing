using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class IntegralEpsilonDominationDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Some(string name, Formula type) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula At(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula Lam(string name, Formula body) =>
        Seq(Open, V(name), Sp, Mapsto, Sp, body, Close);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Times(Formula a, Formula b) => Seq(a, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Fn => At(V("f"), V("n"));
    private static Formula An => At(V("a"), V("n"));
    private static Formula Function => Arrow(V("Omega"), V("Real"));
    private static Formula Sequence => Arrow(V("Nat"), Function);
    private static Formula I(Formula h) => Call("integral", V("mu"), h);
    private static Formula Integrable(Formula h) => Call("Integrable", h, V("mu"));
    private static Formula Tendsto(Formula h) =>
        Call("Tendsto", h, V("atTop"), Call("nhds", D(0)));

    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(All("Omega", Seq(V("Type"), Underscore, Grp(V("u")))),
            OpenBracket, Call("MeasurableSpace", V("Omega")), CloseBracket),
        Seq(All("mu", Call("Measure", V("Omega"))), All("f", Sequence), All("M", V("Real"))),
        Seq(Open, All("n", V("Nat")), Integrable(Fn), Close, Sp, Rightarrow),
        Seq(Call("AE", V("mu"), Lam("x", Tendsto(Lam("n", At(Fn, V("x")))))), Sp, Rightarrow),
        Seq(Open, All("n", V("Nat")), All("x", V("Omega")),
            Le(D(0), At(Fn, V("x"))), Close, Sp, Rightarrow),
        Seq(Open, All("epsilon", V("Real")), D(0), Sp, F.Lt, Sp, V("epsilon"), Sp, Rightarrow),
        Seq(Some("a", Sequence), Some("b", Function)),
        Seq(Open, All("n", V("Nat")), Integrable(An), Close,
            Sp, Land, Sp, Integrable(V("b"))),
        Seq(Land, Sp, Open, All("n", V("Nat")), All("x", V("Omega")),
            Le(D(0), At(An, V("x"))), Close),
        Seq(Land, Sp, Open, All("x", V("Omega")), Le(D(0), At(V("b"), V("x"))), Close),
        Seq(Land, Sp, Open, All("n", V("Nat")), Le(I(An), V("M")), Close),
        Seq(Land, Sp, Open, All("n", V("Nat")), All("x", V("Omega")),
            Le(At(Fn, V("x")), Add(Times(V("epsilon"), At(An, V("x"))),
                At(V("b"), V("x")))), Close, Close, Sp, Rightarrow),
        Tendsto(Lam("n", I(Fn)))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral convergence with epsilon-dependent controls on arbitrary measure spaces.",
        H("Integral convergence under epsilon domination"),
        Blocks(
            Paragraph(Text("The universe u and measurable space Omega are arbitrary. The measure mu need not be finite or sigma-finite. "
                + "The sequence f has type Nat -> Omega -> Real. The bound M is a real number; nonnegativity follows from the control premise. "
                + "For each positive epsilon, a has type Nat -> Omega -> Real and b has type Omega -> Real; "
                + "both may depend on epsilon. AE(mu,P) means that P holds mu-almost everywhere, "
                + "Integrable means real Bochner integrability, and integral(mu,h) is the real Bochner integral of h.")),
            Describe.Lean(DescribeId.Create("epsilon-dependent-integral-domination"),
                DeclarationHandle.Create("D5/S3/Topology/Measures/IntegralEpsilonDomination.tendsto_integral_of_epsilon_domination"),
                H("A common integral budget with varying pointwise controls"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every f(n) is integrable and pointwise nonnegative, and f(n,x) tends to zero almost everywhere. "
                        + "For every epsilon > 0 there are nonnegative integrable controls a(n) and b such that "
                        + "f(n,x) <= epsilon a(n,x) + b(x) for every n and x, with integral(a(n)) <= M. "
                        + "The same finite M works for all epsilon and n. Then the integrals of f(n) tend to zero.")),
                    Paragraph(Text("Fix epsilon and truncate to F(n,x) = max(f(n,x) - epsilon a(n,x),0). "
                        + "The inequalities 0 <= F(n,x) <= f(n,x) give almost-everywhere convergence to zero. "
                        + "The fixed-epsilon bound F(n,x) <= b(x) supplies dominated convergence. "
                        + "The remaining integral is at most epsilon M, so letting epsilon decrease proves the result. "
                        + "No pointwise convergence of a(n), common choice of a or b across epsilon, "
                        + "or uniform bound on integral(b) across epsilon is assumed.")),
                    Paragraph(Text("This isolates the classical truncation argument used in Brézis–Lieb splitting. "
                        + "Both nonlinear complex cancellation and positive-power splitting follow by applying this criterion "
                        + "to the norm of the corresponding defect. No mathematical originality is claimed."))),
                DescribeRole.Theorem))));
}
