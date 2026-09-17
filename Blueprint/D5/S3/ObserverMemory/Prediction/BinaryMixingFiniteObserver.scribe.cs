using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class BinaryMixingFiniteObserverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive binary mixing rate admits a finite deterministic observer with arbitrarily small uniform next-report prediction error.",
        H("Finite observers for positive binary mixing"),
        Blocks(
            Paragraph(Text(
                "Fix emission and mixing parameters p and r strictly between zero and one half. "
                + "The hidden prior is (1/2,1/2). The old hidden bit emits before it flips: "
                + "report zero has emission weights p and 1-p on hidden zero and hidden one, "
                + "and report one exchanges these weights. The flip probability is r. "
                + "Chronological words include the empty word.")),
            Paragraph(Text(
                "Write v(w) for the resulting unnormalized hidden column, Z(w) for the sum "
                + "of its two coordinates, and f(w)=Z(w0)/Z(w) for the next-zero prediction. "
                + "These are the transfer, wordVector, wordMass and prediction of the binary "
                + "mixing process. Both coordinates stay positive. The mass of the empty "
                + "word is one, and Z(w0)+Z(w1)=Z(w), so the ratios are actual normalized "
                + "conditional probabilities for every finite history.")),
            Paragraph(Text(
                "An observer consists of a finite set S, an initial state s0, fixed updates "
                + "T0 and T1, and a fixed real readout t. Write s(w) for its chronological "
                + "run, starting at s(empty)=s0 and satisfying s(wb)=Tb(s(w)). "
                + "The initial state makes S nonempty, and all evolving memory resides in S.")),
            Describe.Lean(
                DescribeId.Create("finite-suffix-observer-exists"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Prediction/BinaryMixingFiniteObserver."
                    + "finite_suffix_observer_exists"),
                H("Uniform finite-state approximation"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state set, updates and readout may depend on p, r and the "
                        + "positive error allowance, but the same tables serve every finite "
                        + "history. No lower bound on history probability is imposed. "
                        + "This is mathematical existence with exact real tables.")),
                    Paragraph(Text(
                        "Use the log odds of the two positive hidden masses. Emission adds "
                        + "the logarithm of the ratio of its weights; mixing then applies "
                        + "G(x)=log(r+(1-r)exp(x))-log(1-r+r exp(x)). Its derivative is "
                        + "positive and at most eta=1-2r. Indeed, the derivative denominator "
                        + "minus exp(x) is r(1-r)(exp(x)-1)^2. Also, the absolute value of "
                        + "G is bounded by B=log((1-r)/r). A common word of length k "
                        + "therefore contracts differences of log odds by eta^k.")),
                    Paragraph(Text(
                        "The normalized hidden-one mass is the sigmoid of its log odds. "
                        + "The sigmoid derivative is at most one quarter, and the next-zero "
                        + "prediction is p plus (1-2p) times this hidden-one mass. Consequently, "
                        + "discarding a prefix before a shared suffix of length k changes "
                        + "the prediction by at most C eta^k, where C=(1-2p)B/4.")),
                    Paragraph(Text(
                        "Choose k so that this geometric bound is within the error "
                        + "allowance. Take S to be all Boolean lists of length at most k, "
                        + "start at the empty list, and update by appending the report and "
                        + "retaining the last k symbols. The readout at a stored list is "
                        + "its exact prediction from the fixed prior. Induction identifies "
                        + "the run state with the last k reports, or with the whole history "
                        + "during startup. Empty and short histories are predicted exactly; "
                        + "longer histories satisfy the geometric bound. Startup length "
                        + "is part of the finite state, including the one-state case k=0."))),
                DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(Id("R")));
    private static Formula Half => Seq(Frac, Grp(D(1)), Grp(D(2)));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, Formula arg) => Seq(Id(name), Par(arg));
    private static Formula Indexed(string name, byte digit) => Seq(Id(name), Underscore, Grp(D(digit)));

    private static Formula ResultFormula()
    {
        var p = Id("p");
        var r = Id("r");
        var e = Varepsilon;
        var s = Id("S");
        var q = Id("z");
        var w = Id("w");
        var words = Seq(OpenBrace, D(0), Comma, D(1), CloseBrace, Caret, Grp(Star));
        var error = Seq(Lvert, Sp, Call("t", Call("s", w)), Minus, Call("f", w), Rvert);
        return Disp(Seq(
            Forall, Sp, p, Comma, r, Comma, e, InMacro, Sp, Real, Comma, Esc,
            Par(Seq(D(0), Sp, Lt, Sp, p, Sp, Lt, Sp, Half, Sp, Land, Sp,
                D(0), Sp, Lt, Sp, r, Sp, Lt, Sp, Half, Sp, Land, Sp,
                D(0), Sp, Lt, Sp, e)), Sp, Rightarrow, Sp, Esc,
            Par(Seq(Forall, Sp, w, InMacro, Sp, words, Comma, Sp,
                D(0), Sp, Lt, Sp, Call("Z", w))), Sp, Land, Sp, Esc,
            Exists, Sp, s, Comma, Sp,
            OpenBracket, Operatorname, Grp(Id("Fintype")), Sp, s, CloseBracket, Comma, Sp,
            Exists, Sp, Indexed("s", 0), InMacro, Sp, s, Comma, Esc,
            Exists, Sp, Indexed("T", 0), Comma, Indexed("T", 1), Colon, Sp,
            s, Sp, To, Sp, s, Comma, Sp,
            Exists, Sp, Id("t"), Colon, Sp, s, Sp, To, Sp, Real, Comma, Esc,
            Par(Seq(Forall, Sp, q, InMacro, Sp, s, Comma, Sp,
                D(0), Sp, Leq, Sp, Call("t", q), Sp, Leq, Sp, D(1))), Sp, Land, Sp, Esc,
            Forall, Sp, w, InMacro, Sp, words, Comma, Sp, error, Sp, Leq, Sp, e));
    }
}
