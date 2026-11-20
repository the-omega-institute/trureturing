using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class ChenFixedOrderSamplingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Probability/ChenFixedOrderSampling.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Type => Seq(Operatorname, Grp(V("Type")));
    private static Formula M => V("m");
    private static Formula A => V("A");
    private static Formula S => V("S");
    private static Formula J => V("j");
    private static Formula Parenthesized(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Sp, Colon, Sp, type);
    private static Formula All(Formula name, Formula type) => Seq(Forall, Sp, Typed(name, type), Comma, Sp);
    private static Formula AllStages => All(M, Nat);
    private static Formula AtStage(string name) => Call(name, M);
    private static Formula Population => AtStage("Population");
    private static Formula Sample => AtStage("Sample");
    private static Formula Draw => AtStage("Draw");
    private static Formula SampleSize => AtStage("sampleSize");
    private static Formula Value => Call("populationValue", M, J);
    private static Formula Estimator => Call("estimator", M, S);
    private static Formula PropertySet(Formula body) => Seq(OpenBrace, body, CloseBrace);
    private static Formula Qualified(string owner, string member) => Seq(Operatorname, Grp(V(owner), Dot, V(member)));
    private static Formula Val(Formula value) => Seq(value, Dot, V("val"));
    private static Formula Card(Formula value) => Call("card", value);
    private static Formula AsMeasure(Formula value, Formula carrier) =>
        Parenthesized(Typed(value, Call("Measure", carrier)));
    private static Formula Uniform(Formula carrier) =>
        Call("uniformOn", Parenthesized(Typed(Qualified("Set", "univ"), Call("Set", carrier))));
    private static Formula DistinctDraw => Seq(V("d"), Sp, InMacro, Sp, AtStage("distinct"));
    private static Formula ErasedDraw => Call("eraseOrder", M, V("d"));
    private static Formula DrawImage =>
        new Formula.Apply(Qualified("Finset", "image"), [V("d"), Qualified("Finset", "univ")]);
    private static Formula Integral(Formula binder, Formula integrand) =>
        Seq(Int, Sp, binder, Comma, Sp, integrand, Sp, V("d"), Uniform(Sample));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform fixed-size sampling and the stratum inclusion identities for Chen's fixed-order problem.",
        H("Fixed-size samples from two balanced strata"),
        Blocks(
            Definition("chen-sample-size", "sampleSize", "Sample size",
                Seq(AllStages, Typed(SampleSize, Nat), Sp, Eq, Sp,
                    new Formula.Power(Parenthesized(Seq(M, Plus, D(1))), D(2))),
                "The increasing square sizes index the sampling designs."),
            Definition("chen-stratum-size", "stratumSize", "Size of each stratum",
                Seq(AllStages, Typed(AtStage("stratumSize"), Nat), Sp, Eq, Sp,
                    new Formula.Power(SampleSize, D(3))),
                "Both strata have this size, so the sample occupies a vanishing fraction of the population."),
            Definition("chen-population", "Population", "Population labels",
                Seq(AllStages, Typed(Population, Type), Sp, Eq, Sp, Call("Fin", D(2)), Sp, Times, Sp,
                    Call("Fin", AtStage("stratumSize"))),
                "The first coordinate records the stratum and the second the label within it."),
            Definition("chen-sample", "Sample", "Subsets of the prescribed size",
                Seq(AllStages, Typed(Sample, Type), Sp, Eq, Sp,
                    Call("Subtype", Seq(Parenthesized(Typed(S, Call("Finset", Population))), Sp,
                        Mapsto, Sp, Card(S), Sp, Eq, Sp, SampleSize))),
                "The cardinality condition is carried with the underlying finite subset."),
            Definition("chen-population-value", "populationValue", "Values of the two strata",
                Seq(AllStages, All(J, Population), Typed(Value, Real), Sp, Eq, Sp,
                    Call("ite", Seq(Seq(J, Dot, D(1)), Sp, Eq, Sp, D(0)), D(1), Seq(Minus, D(1)))),
                "The opposite values make the two equal strata balance."),
            Definition("chen-population-mean", "populationMean", "Population mean",
                Seq(AllStages, Typed(AtStage("populationMean"), Real), Sp, Eq, Sp,
                    new Formula.Fraction(Seq(new Formula.Subscript(Sum, Typed(J, Population)), Sp, Value),
                        Parenthesized(Typed(new Formula.Apply(Qualified("Fintype", "card"), [Population]), Real)))),
                "Every label enters with the same weight."),
            Definition("chen-estimator", "estimator", "Centered and scaled sample mean",
                Seq(AllStages, All(S, Sample), Typed(Estimator, Real), Sp, Eq, Sp,
                    Sqrt, Grp(Typed(SampleSize, Real)), Sp, Cdot, Sp, Parenthesized(Seq(
                        new Formula.Fraction(
                            Seq(new Formula.Subscript(Sum, Seq(J, Sp, InMacro, Sp, Val(S))), Sp, Value),
                            Parenthesized(Typed(SampleSize, Real))),
                        Sp, Minus, Sp, AtStage("populationMean")))),
                "The centering and scaling are shared by the two designs."),
            Definition("chen-inclusion-event", "inclusion", "Sample inclusion event",
                Seq(AllStages, All(A, Call("Finset", Population)),
                    Typed(Call("inclusion", M, A), Call("Set", Sample)), Sp, Eq, Sp,
                    PropertySet(Seq(S, Sp, Mid, Sp, A, Sp, Subseteq, Sp, Val(S)))),
                "The prescribed subset may be empty."),
            Definition("chen-uniform-sample-law", "uniformSampleMeasure", "Uniform sampling law",
                new Formula.Aligned([
                    Seq(AllStages, Typed(AtStage("uniformSampleMeasure"), Call("ProbabilityMeasure", Sample)), Comma),
                    Seq(AsMeasure(AtStage("uniformSampleMeasure"), Sample), Sp, Eq, Sp, Uniform(Sample))
                ]),
                "Each sample of the prescribed size receives the same mass."),
            Definition("chen-ordered-draw", "Draw", "Ordered draws with replacement",
                Seq(AllStages, Typed(Draw, Type), Sp, Eq, Sp,
                    new Formula.TypeArrow(Call("Fin", SampleSize), Population)),
                "The position index allows a label to occur more than once."),
            Definition("chen-distinct-event", "distinct", "Distinctness event of an ordered draw",
                Seq(AllStages, Typed(AtStage("distinct"), Call("Set", Draw)), Sp, Eq, Sp,
                    PropertySet(Seq(V("d"), Sp, Mid, Sp,
                        new Formula.Apply(Qualified("Function", "Injective"), [V("d")])))),
                "Conditioning on injectivity gives draws without replacement."),
            Definition("chen-erase-order", "eraseOrder", "Erasing order",
                new Formula.Aligned([
                    Seq(AllStages, All(V("d"), Draw), Typed(ErasedDraw, Sample), Comma),
                    Seq(DistinctDraw, Sp, Rightarrow, Sp, ErasedDraw, Sp, Eq, Sp,
                        Langle, DrawImage, Comma, Sp,
                        Typed(V("h"), Seq(Card(DrawImage), Sp, Eq, Sp, SampleSize)), Rangle, Comma),
                    Seq(Neg, Parenthesized(DistinctDraw), Sp, Rightarrow, Sp, ErasedDraw, Sp, Eq, Sp,
                        new Formula.Apply(Qualified("Classical", "choice"),
                            [Typed(V("inferInstance"), Call("Nonempty", Sample))]))
                ]),
                "Injectivity gives the cardinality proof h. Only values on the distinctness event "
                + "contribute under the conditioned law."),
            Result("chen-positive-sample-size", "sampleSize_pos", "Positive sample size",
                Seq(AllStages, D(0), Sp, Lt, Sp, SampleSize),
                "The sample size is positive at every stage."),
            Result("chen-sample-fits-stratum", "sampleSize_le_stratumSize", "Sample size bounded by stratum size",
                Seq(AllStages, SampleSize, Sp, Leq, Sp, AtStage("stratumSize")),
                "The sample fits within either stratum since each stratum has the cube of the sample size."),
            Result("chen-sample-size-tends-to-infinity", "sampleSize_tendsto", "Divergence of sample sizes",
                Call("Tendsto", Seq(Operatorname, Grp(V("sampleSize"))),
                    Seq(Operatorname, Grp(V("atTop"))), Seq(Operatorname, Grp(V("atTop")))),
                "The squares of the positive stage indices tend to infinity."),
            Result("chen-zero-population-mean", "populationMean_eq_zero", "Zero population mean",
                Seq(AllStages, AtStage("populationMean"), Sp, Eq, Sp, D(0)),
                "The two strata have equal size and opposite values, so the population mean is zero."),
            Result("chen-erase-order-image", "eraseOrder_val", "Finite image of a distinct draw",
                Seq(AllStages, All(V("d"), Draw), DistinctDraw, Sp, Rightarrow, Sp,
                    Val(ErasedDraw), Sp, Eq, Sp, DrawImage),
                "For each injective ordered draw, its unordered sample is exactly the finite image of the draw."),
            Result("chen-condition-and-erase-order", "map_eraseOrder_cond_uniform",
                "Uniform law on fixed-size subsets",
                Seq(AllStages, new Formula.Apply(Qualified("Measure", "map"), [
                    AtStage("eraseOrder"),
                    new Formula.Apply(Qualified("ProbabilityTheory", "cond"), [Uniform(Draw), AtStage("distinct")])
                ]), Sp, Eq, Sp, Uniform(Sample)),
                "Condition the uniform law of ordered draws on having distinct labels, "
                    + "then erase order. Every subset of the required size has the same "
                    + "number of orderings, giving the uniform subset law."),
            Result("chen-inclusion-polynomial", "exists_inclusionPolynomial", "Inclusion polynomial",
                new Formula.Aligned([
                    Seq(AllStages, All(A, Call("Finset", Population)), Exists, Sp,
                        Typed(V("p"), Call("Polynomial", Real)), Comma, Sp,
                        Call("natDegree", V("p")), Sp, Leq, Sp, Card(A), Sp, Land),
                    Parenthesized(new Formula.Aligned([
                        Seq(All(V("f"), new Formula.TypeArrow(Real, Real)),
                            Integral(Seq(S, Sp, InMacro, Sp, Call("inclusion", M, A)), Call("f", Estimator)), Sp, Eq),
                        Seq(Quad, Integral(Typed(S, Sample),
                            Seq(new Formula.Apply(Qualified("Polynomial", "eval"), [Estimator, V("p")]),
                                Sp, Cdot, Sp, Call("f", Estimator))))
                    ]))
                ]),
                "On each cell of fixed positive-stratum count, the inclusion fraction is the product "
                    + "of two ratios of binomial coefficients. The two counts are affine in the "
                    + "estimator, giving the degree bound. Summing over the cells gives the restricted integral."))));

    private static DocumentBlock.Describe Definition(string id, string declaration, string title, Formula formula, string explanation) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    private static DocumentBlock.Describe Result(
        string id, string declaration, string title, Formula formula, string explanation) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
}
