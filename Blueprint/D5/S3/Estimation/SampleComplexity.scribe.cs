using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation;

internal sealed class SampleComplexityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Estimation/SampleComplexity",
            "The finite n-sample testing floors culminate in a universal Bretagnolle--Huber lower bound on the divergence budget required to attain a prescribed error."),
        H("Sample Complexity from Finite Testing-Error Floors"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("every-accurate-iid-test-requires-a-divergence-budget"),
                H("Every accurate i.i.d. test requires a divergence budget"),
                LeanTheorem(
                    "D5/S3/Estimation/SampleComplexity.sample_complexity_bretagnolle_huber"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Forall, Sp, F.Id("n"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, RowBreak,
                    Forall, Sp, F.Id("A"), Colon, Sp,
                    Operatorname, Grp(F.Id("Finset")), Open,
                    Operatorname, Grp(F.Id("IidSpace")),
                    Open, Iota, Comma, Sp, F.Id("n"), Close, Close, Comma, RowBreak,
                    Forall, Sp, Varepsilon, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1), Close,
                    Sp, Land, Sp,
                    Open,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(1), Close,
                    Sp, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Lt, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Lt, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp, RowBreak,
                    Open, D(0), Lt, Sp, Varepsilon, Sp, Lt, Sp, D(1), Close,
                    Sp, Land, Sp, RowBreak,
                    Open,
                    Sum, Sp, Underscore,
                    Grp(F.Id("z"), InMacro, Sp, F.Id("A")), Sp,
                    Operatorname, Grp(F.Id("iidPower")),
                    Open, F.Id("p"), Comma, Sp, F.Id("n"), Comma, Sp, F.Id("z"), Close,
                    Plus,
                    Sum, Sp, Underscore,
                    Grp(
                        F.Id("z"), InMacro, Sp,
                        F.Id("A"), Caret, F.Id("c")), Sp,
                    Operatorname, Grp(F.Id("iidPower")),
                    Open, F.Id("q"), Comma, Sp, F.Id("n"), Comma, Sp, F.Id("z"), Close,
                    Le, Sp, Varepsilon, Close,
                    Close, Sp, Rightarrow, Sp, RowBreak,
                    Log, Sp, Open,
                    Frac, Grp(D(1)),
                    Grp(
                        D(2), Sp, Varepsilon, Minus,
                        Varepsilon, Caret, Grp(D(2))),
                    Close,
                    Le, Sp,
                    F.Id("n"), Sp, Cdot, Sp,
                    F.Id("D"), Underscore,
                    Grp(Operatorname, Grp(F.Id("KL"))),
                    Open, F.Id("p"), Sp, Vert, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The preceding waves pinned the single-trial testing floor at one minus " +
                        "total variation and then re-expressed that floor through relative " +
                        "entropy. Frozen additivity on independent powers subsequently made the " +
                        "divergence scale linearly with the sample count. This module closes that " +
                        "arc: it first states the resulting floor at each sample count and then " +
                        "inverts the informative floor.")),
                    Paragraph(Text(
                        "The two n-sample floors are chained corollaries, not new inequalities. " +
                        "The declaration iid_testing_error_pinsker composes the frozen " +
                        "single-trial Pinsker floor with frozen n-fold KL additivity to give total " +
                        "error at least 1-sqrt(n D/2). The declaration " +
                        "iid_testing_error_bretagnolle_huber makes the same composition with the " +
                        "frozen Bretagnolle--Huber floor and gives total error at least " +
                        "1-sqrt(1-exp(-n D)). The module consumes both frozen ingredients and " +
                        "re-derives neither; the change of parameter from D to n D is a " +
                        "composition, not a discovery.")),
                    Paragraph(Text(
                        "The inversion is this wave's contribution, and it answers the question " +
                        "one ordinarily asks. Rather than fixing n and asking how small the error " +
                        "can be, sample_complexity_bretagnolle_huber fixes a target error epsilon. " +
                        "If any test event A on n independent trials has total error at most " +
                        "epsilon, then log(1/(2 epsilon-epsilon^2)) is at most n times the KL " +
                        "divergence. The event A is universally quantified. Consequently the " +
                        "bound constrains every possible test, which makes it a complexity " +
                        "statement rather than a performance guarantee for one selected " +
                        "procedure.")),
                    Paragraph(Text(
                        "The scale is already substantive at ordinary accuracy levels. At " +
                        "epsilon=0.01 the logarithmic threshold is approximately 3.92, so laws " +
                        "with KL divergence 0.1 require about 40 trials. At epsilon=0.05 the same " +
                        "divergence gives a requirement of about 23 trials. More generally, the " +
                        "required divergence budget grows on the order of log(1/epsilon) as the " +
                        "target error tends to zero.")),
                    Paragraph(Text(
                        "The conclusion is deliberately a lower bound on the product n D rather " +
                        "than a quotient-form lower bound on n. Dividing by D would require a " +
                        "nonzero-divergence side condition. Retaining the product avoids that " +
                        "condition and remains faithful when the two laws are identical: then " +
                        "D=0, and no finite number of independent trials can meet an error target " +
                        "strictly below one.")),
                    Paragraph(Text(
                        "Bretagnolle--Huber is essential to the inversion. The frozen theorem " +
                        "pinsker_floor_nonpos_of_two_le shows that the Pinsker floor is " +
                        "nonpositive once its divergence argument reaches two. Thus it loses all " +
                        "invertible information precisely when multiplication by the sample count " +
                        "makes n D large. By contrast, the frozen theorem " +
                        "bretagnolle_huber_floor_pos shows that the Bretagnolle--Huber floor stays " +
                        "strictly positive at every finite divergence. Only that floor survives " +
                        "the inversion, which is the payoff of the earlier Bretagnolle--Huber " +
                        "wave.")),
                    Paragraph(Text(
                        "The range 0<epsilon<1 is forced by the proof rather than chosen for " +
                        "convenience. The upper inequality makes 1-epsilon positive, as required " +
                        "when the square-root comparison is squared. Together the two strict " +
                        "inequalities make 2 epsilon-epsilon^2=epsilon(2-epsilon) positive, so " +
                        "logarithmic monotonicity applies. The upper inequality also gives " +
                        "2 epsilon-epsilon^2=1-(1-epsilon)^2<1; hence the logarithm in the " +
                        "conclusion is strictly positive and the lower bound is non-trivial. The " +
                        "remaining assumptions are exactly the collapsed union of those used by " +
                        "the frozen components. N-fold additivity requires strict positivity and " +
                        "normalization, whereas the single-trial floors require nonnegativity, " +
                        "normalization, and discrete absolute continuity. Strict positivity " +
                        "absorbs both nonnegativity and absolute continuity, because a strictly " +
                        "positive reference law never vanishes. Both normalizations remain, since " +
                        "positivity alone does not imply unit mass.")),
                    Paragraph(Text(
                        "The module reuses the imported IidSpace and iidPower constructions and " +
                        "declares no definition of its own. It proves no matching upper bound and " +
                        "exhibits no test attaining the rate. No minimax formulation, " +
                        "multi-hypothesis or Assouad-style generalization, or measure-theoretic " +
                        "analogue is claimed. Relative entropy and the logarithmic threshold use " +
                        "the natural logarithm, so the units are nats.")))))));
}
