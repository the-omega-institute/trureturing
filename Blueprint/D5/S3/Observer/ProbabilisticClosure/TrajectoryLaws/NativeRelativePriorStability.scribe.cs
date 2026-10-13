using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class NativeRelativePriorStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula mu = F.Id("mu"), nu = F.Id("nu"), zeta = F.Id("zeta"), k = F.Id("k");
        Formula h = F.Id("h"), c = F.Id("c"), s = F.Id("s");
        Formula lower = Call("ofReal", Seq(D(1), Minus, zeta));
        Formula upper = Call("ofReal", Seq(D(1), Plus, zeta));
        Formula priors = All(And(
            Le(Multiply(lower, Call("at", mu, k)), Call("at", nu, k)),
            Le(Call("at", nu, k), Multiply(upper, Call("at", mu, k)))), ("k", "Depth"));
        Formula conclusion = Le(Call("measurableTotalVariation",
            Call("rawTarget", mu, h, c, s), Call("rawTarget", nu, h, c, s)),
            Call("ofReal", new Formula.Fraction(zeta, Seq(D(1), Minus, zeta))));
        Formula hypotheses = And(Le(D(0), zeta), And(Seq(zeta, Lt, Sp, D(1)),
            And(priors, Seq(Call("run", h), Eq, Call("some", c)))));
        Formula statement = All(Imp(hypotheses, conclusion), ("mu", "PMFDepth"),
            ("nu", "PMFDepth"), ("zeta", "Real"), ("h", "ListOperation"),
            ("c", "AcquiredNativeState"), ("s", "ActivePhase"));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Relative-prior stability of complete native conditional tails.",
            H("Relative-prior stability of complete native conditional tails"), Blocks(
                Paragraph(Text("PMFDepth is a probability mass function on the original positive integer Depth carrier, with arbitrary finite or countable support. ListOperation means the original List Operation. at(mu,k)=mu(k), ofReal is the canonical map into ENNReal, and TV is the event-supremum measurableTotalVariation. Both priors use the same rate(k), original source history cylinder and unread stopped-tail map. No bounded support, finite-depth cutoff or lower bound on individual positive prior masses is required.")),
                Paragraph(Text("The relative comparison includes common zero masses. For every finite legal h with run(h)=some(c), the native history normalizer is positive under each PMF. The complete rawTarget is the original jointLaw conditioned on nativeEvent(h,c), mapped by validStopped(s,rawTail(omega,length(readLetters(h)))). It retains every finite lawful completion and the unique infinite noncompletion coordinate. Neither an auxiliary posterior model nor a clipped law replaces that target.")),
                Describe.Lean(DescribeId.Create("native-relative-prior-tail"),
                    DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeRelativePriorStability.native_relative_prior_tail"),
                    H("All finite legal histories and both active phases"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The original countable depth mixture inherits both event-wise prior bounds. Conditioning on the same positive history event gives the two normalized inequalities (1-zeta)P(E)<=(1+zeta)Q(E) and (1-zeta)Q(E)<=(1+zeta)P(E). Apply them to E and its complement; probability normalization bounds both directed differences by zeta. Taking the measurable-event supremum and mapping through the original validStopped map gives TV<=ofReal(zeta), which implies the displayed source bound zeta/(1-zeta). This estimate is uniform in history mass and length, including rare histories."))), DescribeRole.Theorem),
                Paragraph(Text("This is the complete raw stopped-configuration law subclause of Theorem 7.2 in RECURSIVE_RELATIONAL_OBSERVATION_ENDPOINT_FLOOR_HISTORY_LOCALIZATION. Rendering to full transcripts, observer row comparisons, both law-error orders, capped and uncapped risks and Phi, witness transfer and acquisition-cap certificates remain separate obligations. No assertion about a runtime prior oracle, effective computation, sharp optimal constant or research originality is made. The source-independent private-row and full-transcript transport suppliers are NativeObserverJointLaw.native_history_risk_transport and NativeFullResidual.full_renderer_tv.")))));
    }
    private static Formula Le(Formula a, Formula b) => Seq(a, Leq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Open, a, Close, Land, Open, b, Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Close, Rightarrow, Open, b, Close);
    private static Formula All(Formula body, params (string Name, string Type)[] xs)
    {
        for (var i = xs.Length - 1; i >= 0; i--)
            body = Seq(Forall, Sp, F.Id(xs[i].Name), Colon, Sp, F.Id(xs[i].Type), Comma, Sp,
                Open, body, Close);
        return body;
    }
    private static Formula Seq(params Formula[] xs) => F.Seq(xs);
    private static Formula Call(string name, params Formula[] xs)
    {
        var parts = new Formula[xs.Length * 2 - 1];
        for (var i = 0; i < xs.Length; i++)
        {
            parts[i * 2] = xs[i];
            if (i > 0) parts[i * 2 - 1] = Comma;
        }
        return Seq(Operatorname, Grp(F.Id(name)), Open, Seq(parts), Close);
    }
}
