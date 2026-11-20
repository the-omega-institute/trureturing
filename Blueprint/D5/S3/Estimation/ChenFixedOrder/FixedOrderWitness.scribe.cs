using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ChenFixedOrder;

internal sealed class FixedOrderWitnessDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/ChenFixedOrder/FixedOrderWitness";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Estimation/chen2026fixedorderinclusion");

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Parenthesized(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula AtStage(string family) => Call(family, V("m"));
    private static Formula AllStages => Seq(Forall, Sp, V("m"), Colon, Sp, Nat, Comma, Sp);
    private static Formula Sample => AtStage("Sample");
    private static Formula Gaussian => Seq(Operatorname, Grp(V("standardGaussian")));
    private static Formula AtTop => Seq(Operatorname, Grp(V("atTop")));
    private static Formula StageFunction(Formula value) => Seq(V("m"), Sp, Mapsto, Sp, value);
    private static Formula AsSampleMeasure(string design) =>
        Parenthesized(Seq(AtStage(design), Sp, Colon, Sp, Call("Measure", Sample)));
    private static Formula EventMass(string design) =>
        new Formula.Apply(AsSampleMeasure(design), [Call("inclusion", V("m"), V("A"))]);
    private static Formula LimitLaw(string design, Formula limit) =>
        Call("Tendsto", StageFunction(new Formula.Apply(
            Seq(Operatorname, Grp(V("ProbabilityMeasure"), Dot, V("map"))),
            [AtStage(design), AtStage("estimator")])),
            AtTop, Call("nhds", limit));

    private static Formula FixedOrderClause() => Parenthesized(new Formula.Aligned([
        Seq(Forall, Sp, V("r"), Colon, Sp, Nat, Comma, Sp,
            D(0), Sp, Lt, Sp, V("r"), Sp, Rightarrow, Sp),
        Seq(Quad, Exists, Sp, V("P"), Comma, V("Q"), Colon, Sp,
            new Formula.Subscript(Prod, Seq(V("m"), Colon, Nat)), Sp,
            Call("ProbabilityMeasure", Sample), Comma, Sp,
            Nu, Sp, Colon, Sp, Call("ProbabilityMeasure", Real), Comma, Sp,
            Left, Open, new Formula.Aligned([
                Seq(Parenthesized(Seq(AllStages, AsSampleMeasure("P"), Sp, Eq, Sp,
                    Call("uniformOn", Seq(Operatorname, Grp(V("Set"), Dot, V("univ")))))),
                    Sp, Land),
                Seq(Parenthesized(new Formula.Aligned([
                    Seq(AllStages, Forall, Sp, V("A"), Colon, Sp,
                        Call("Finset", AtStage("Population")), Comma, Sp, Call("card", V("A")),
                        Sp, Leq, Sp, V("r"), Sp, Rightarrow),
                    Seq(Quad, EventMass("P"), Sp, Eq, Sp, EventMass("Q"))
                ])), Sp, Land),
                Seq(LimitLaw("P", Gaussian), Sp, Land),
                Seq(LimitLaw("Q", Nu), Sp, Land, Sp, Nu, Sp, Neq, Sp, Gaussian)
            ]), Right, Close)
    ]));

    private static Formula Witness() => new Formula.Aligned([
        Seq(Call("Tendsto", V("sampleSize"), AtTop, AtTop), Sp, Land, Sp,
            Call("Tendsto", StageFunction(new Formula.Apply(
                Seq(Operatorname, Grp(V("Fintype"), Dot, V("card"))), [AtStage("Population")])),
                AtTop, AtTop), Sp, Land),
        Seq(Parenthesized(Seq(AllStages, AtStage("populationMean"), Sp, Eq, Sp, D(0))), Sp, Land),
        FixedOrderClause()
    ]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-order inclusion agreement permits distinct weak limits of a common estimator.",
        H("Chen's fixed-order inclusion conjecture"),
        Blocks(
            Paragraph(Text(
                "At stage m, Population(m) has two equal strata, each of size sampleSize(m) cubed, "
                + "with values +1 and -1. The sample size is (m+1)^2. Sample(m) is the type of "
                + "all subsets of Population(m) of that size. The estimator is the sample mean minus "
                + "the population mean, multiplied by the square root of the sample size.")),
            Paragraph(Text(
                "The event inclusion(m,A) consists of the samples at stage m that contain A. "
                + "The uniform measure assigns equal mass to all samples of the prescribed size. "
                + "The map sends each design through the common estimator, and convergence of "
                + "probability measures is weak convergence.")),
            Describe.Lean(
                DescribeId.Create("chen-fixed-order-witness-proposition"),
                DeclarationHandle.Create(Module + ".fixedOrderWitness"),
                H("The proposition"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned(
                    [Seq(V("fixedOrderWitness"), Sp, Iff), Witness()]))),
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
                StatementSource.FromAuthor(Disp(Witness())),
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
