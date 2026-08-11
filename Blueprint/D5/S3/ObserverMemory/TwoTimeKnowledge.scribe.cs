using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory;

internal sealed class TwoTimeKnowledgeDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix = "D5/S3/ObserverMemory/TwoTimeKnowledge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/ObserverMemory/TwoTimeKnowledge",
            "The finite forgetting certificate instantiates semantic loss of observer-fiber constancy."),
        H("Two-Time Knowledge and Forgetting"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("finite-certificate-instantiates-two-time-forgetting"),
                H("The finite certificate instantiates two-time forgetting"),
                LeanTheorem(LeanPrefix + "finite_certificate_instantiates_forgot"),
                CertificateBridgeFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Let s0 be the imported initial Remember certificate and s1 the imported "
                        + "certificate after its Forget action. The frozen transition theorem "
                        + "executes that action from s0 to s1. The semantic interpretation maps "
                        + "Boolean false and true to those two certificate states, reads the world "
                        + "bit at s0, and uses a constant readout at s1.")),
                    Paragraph(Text(
                        "For the unit event with its Boolean world value and universal complete "
                        + "ledger, the same concrete state pair therefore satisfies Forgot. The "
                        + "target certificate also computes to ForgottenLogged. This is a derived "
                        + "model-satisfies-semantics bridge; it does not define Forgot as a cognitive "
                        + "state label or as an audit bit.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("forgot-normalizes-to-a-later-fiber-counterexample"),
                H("Forgot normalizes to a later-fiber counterexample"),
                LeanTheorem(LeanPrefix + "forgot_iff_later_fiber_counterexample"),
                ForgettingFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Forgot is defined by strict time order, persistence in the complete ledger, "
                        + "early knowledge, and later nonknowledge. Knows is itself defined as "
                        + "Function.FactorsThrough. This secondary corollary unfolds those two "
                        + "definitions and classically converts later failure of fiber constancy "
                        + "into two worlds on one readout fiber with different event values.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Function.FactorsThrough for fiber constancy and "
                        + "Function.factorsThrough_iff for its factor-map form. Searches also "
                        + "checked Function.FactorsThrough.extend_comp, "
                        + "Function.not_injective_iff, Classical.not_forall, and Set.Icc. No "
                        + "library declaration performs this domain-specific normalization.")),
                    Paragraph(Text(
                        "The equivalence exposes the quantifiers already present in the definitions; "
                        + "it is not an independent characterization of forgetting. In particular, "
                        + "it does not identify forgetting with a state label, ledger deletion, "
                        + "physical erasure, or a recall transition.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("later-knowledge-pulls-back-along-readout-factorization"),
                H("Later knowledge pulls back along readout factorization"),
                LeanTheorem(
                    LeanPrefix + "knows_of_later_readout_factors_through_earlier"),
                TransportFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Suppose the later readout is constant on every earlier readout fiber, so the "
                    + "later readout factors through the earlier one. Worlds equal under the "
                    + "earlier readout are then equal under the later readout. If the event value "
                    + "is constant on every later fiber, it is consequently constant on every "
                    + "earlier fiber. The implication runs from later knowledge to earlier "
                    + "knowledge under this stated direction of factorization.")))
            ))));

    private static Formula Readout(Formula time, Formula world) => Seq(
        F.Id("r"), Underscore, Grp(time), Open, world, Close);

    private static Formula EventValue(Formula eventId, Formula world) => Seq(
        F.Id("v"), Underscore, Grp(eventId), Open, world, Close);

    private static Formula TimedReadout(Formula time) => Seq(
        F.Id("r"), Underscore, Grp(time));

    private static Formula Knows(Formula eventId, Formula time) => Seq(
        Operatorname, Grp(F.Id("Knows")), Open, eventId, Comma, Sp, time, Close);

    private static Formula Persists(Formula eventId, Formula early, Formula late) => Seq(
        Operatorname, Grp(F.Id("Persists")), Open,
        eventId, Comma, Sp, early, Comma, Sp, late, Close);

    private static Formula Forgot(Formula eventId, Formula early, Formula late) => Seq(
        Operatorname, Grp(F.Id("Forgot")), Open,
        eventId, Comma, Sp, early, Comma, Sp, late, Close);

    private static Formula FactorsThrough(Formula value, Formula readout) => Seq(
        Operatorname, Grp(F.Id("FactorsThrough")), Open,
        value, Comma, Sp, readout, Close);

    private static Formula Transition(Formula source, Formula target) => Seq(
        Operatorname, Grp(F.Id("Transition")), Open,
        source, Comma, Sp, target, Close);

    private static Formula ForgottenLogged(Formula state) => Seq(
        Operatorname, Grp(F.Id("ForgottenLogged")), Open, state, Close);

    private static Formula ForgettingFormula()
    {
        Formula e = F.Id("e");
        Formula t0 = Seq(F.Id("t"), Underscore, Grp(D(0)));
        Formula t1 = Seq(F.Id("t"), Underscore, Grp(D(1)));
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        return Disp(Seq(
            Forall, Sp, e, Comma, Sp, t0, Comma, Sp, t1, Comma, Esc,
            Forgot(e, t0, t1), Sp, Iff, Sp,
            Open,
            t0, Lt, t1, Sp, Land, Sp,
            Persists(e, t0, t1), Sp, Land, RowBreak,
            Open,
            Forall, Sp, x, Comma, Sp, y, Comma, Esc,
            Readout(t0, x), Eq, Readout(t0, y), Sp, Rightarrow, Sp,
            EventValue(e, x), Eq, EventValue(e, y),
            Close, Sp, Land, RowBreak,
            Exists, Sp, x, Comma, Sp, y, Comma, Esc,
            Readout(t1, x), Eq, Readout(t1, y), Sp, Land, Sp,
            EventValue(e, x), Neq, Sp, EventValue(e, y),
            Close, Dot));
    }

    private static Formula TransportFormula()
    {
        Formula e = F.Id("e");
        Formula t0 = Seq(F.Id("t"), Underscore, Grp(D(0)));
        Formula t1 = Seq(F.Id("t"), Underscore, Grp(D(1)));
        return Disp(Seq(
            Forall, Sp, e, Comma, Sp, t0, Comma, Sp, t1, Comma, Esc,
            Open,
            FactorsThrough(TimedReadout(t1), TimedReadout(t0)),
            Sp, Land, Sp, Knows(e, t1),
            Close, Sp, Rightarrow, Sp, Knows(e, t0), Dot));
    }

    private static Formula CertificateBridgeFormula()
    {
        Formula unit = F.Id("unit");
        Formula s0 = Seq(F.Id("s"), Underscore, Grp(D(0)));
        Formula s1 = Seq(F.Id("s"), Underscore, Grp(D(1)));
        Formula early = Seq(Mathrm, Grp(F.Id("false")));
        Formula late = Seq(Mathrm, Grp(F.Id("true")));
        return Disp(Seq(
            Transition(s0, s1), Sp, Land, RowBreak,
            Forgot(unit, early, late), Sp, Land, RowBreak,
            ForgottenLogged(s1), Dot));
    }

}
