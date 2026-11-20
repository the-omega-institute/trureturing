using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ChenFixedOrder;

internal sealed class FixedOrderWitnessDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/ChenFixedOrder/FixedOrderWitness";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Estimation/chen2026fixedorderinclusion");

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula AtStage(string family) => Call(family, F.Id("m"));
    private static Formula Cardinality(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert, Sp);
    private static Formula TendsTo(Formula limit) =>
        Seq(To, Sp, limit);
    private static Formula ForAllStages => Seq(Forall, Sp, F.Id("m"), Colon, Nat, Comma, Sp);
    private static Formula ImageLaw(string design) =>
        Seq(new Formula.Subscript(AtStage("X"), Star), Sp, AtStage(design));
    private static Formula EventMass(string design) =>
        Seq(AtStage(design), Open, Call("E", F.Id("m"), F.Id("A")), Close);

    private static Formula[] WitnessLines() =>
    [
        Seq(AtStage("n"), Sp, TendsTo(Infty), Sp, Land, Sp,
            Cardinality(AtStage("U")), TendsTo(Infty), Sp, Land, Sp,
            Open, ForAllStages, AtStage("mean"), Sp, Eq, Sp, D(0), Close, Sp, Land),
        Seq(Forall, Sp, F.Id("r"), Colon, Nat, Comma, Sp,
            D(0), Sp, Lt, Sp, F.Id("r"), Sp, Rightarrow, Sp),
        Seq(Quad, Exists, Sp, F.Id("P"), Comma, F.Id("Q"), Colon, Sp,
            new Formula.Subscript(Prod, Seq(F.Id("m"), Colon, Nat)), Sp,
            Call("Prob", AtStage("S")), Comma, Sp,
            Nu, Sp, Colon, Sp, Call("Prob", Real), Comma, Sp),
        Seq(Quad, Open, ForAllStages, AtStage("P"), Sp, Eq, Sp, Call("Uniform", AtStage("S")),
            Close, Sp, Land),
        Seq(Quad, Open, ForAllStages, Forall, Sp, F.Id("A"), Colon, Sp,
            Call("Finset", AtStage("U")), Comma, Sp, Cardinality(F.Id("A")), Leq, Sp, F.Id("r"),
            Sp, Rightarrow, Sp, EventMass("P"), Sp, Eq, Sp, EventMass("Q"), Close, Sp, Land),
        Seq(Quad, ImageLaw("P"), Sp, TendsTo(GammaLower), Sp, Land, Sp,
            ImageLaw("Q"), Sp, TendsTo(Nu), Sp, Land, Sp, Nu, Sp, Neq, Sp, GammaLower)
    ];

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-order inclusion agreement permits distinct weak limits of a common estimator.",
        H("Chen's fixed-order inclusion conjecture"),
        Blocks(
            Paragraph(Text(
                "At stage m, the population U(m) has two equal strata, each of size n(m)^3, "
                + "with values +1 and -1. The sample size n(m) is (m+1)^2. S(m) is the set of "
                + "all subsets of U(m) of size n(m). The population mean is mean(m), and X(m) "
                + "is the sample mean minus mean(m), multiplied by the square root of n(m).")),
            Paragraph(Text(
                "Prob denotes probability measures. For a prescribed subset A, E(m,A) is the "
                + "event that the sample contains A. Uniform assigns equal probability to all "
                + "members of S(m). The subscript star denotes pushforward, and gamma is the "
                + "standard Gaussian. Every arrow takes m to infinity. The arrows for probability laws denote weak convergence.")),
            Describe.Lean(
                DescribeId.Create("chen-fixed-order-witness-proposition"),
                DeclarationHandle.Create(Module + ".fixedOrderWitness"),
                H("The proposition"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned(
                    [Seq(F.Id("fixedOrderWitness"), Sp, Iff), .. WitnessLines()]))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Chen poses the question for every fixed order in Sections 1 and 6. "
                    + "The proposition specifies the balanced populations, a uniform baseline, "
                    + "and distinct weak limits of the same estimator under the two designs."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("chen-fixed-order-witness"),
                DeclarationHandle.Create(Module + ".fixedOrderWitness_holds"),
                H("Existence for every fixed positive order"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([.. WitnessLines()]))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The uniform law on fixed-size subsets yields the Gaussian limit. "
                        + "At a fixed order r, tilt each uniform estimator law by the bounded "
                        + "adjugate density of order max(r,2). The density has total integral "
                        + "one and its difference from one integrates to zero against powers "
                        + "through that order.")),
                    Paragraph(Text(
                        "Lift the tilt to the original sample space by evaluating the density "
                        + "at the common estimator. The finite density bridge gives exact "
                        + "inclusion-event equality and identifies the resulting estimator law "
                        + "with the real tilt. Weak continuity of the tilt gives the second limit. "
                        + "The Gaussian separation theorem gives a strictly larger expectation "
                        + "of the residual test under that limit, proving the limits unequal."))),
                DescribeRole.Theorem))));
}
