using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class DetectorSensorStrictAveragingRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation";
    private const string Optimality = "D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality";
    private const string Measurement = "D5/S3/Quantum/Entanglement/TriangleIndependentSourceNoise";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/zhanguptahillery2024detectorsensor");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two optimal three-sensor probes refute strict improvement by coefficient-square averaging.",
        H("Strict averaging fails for optimal detector-sensor probes"),
        Blocks(
            Node("opt-success", "optSuccess", "Optimal discrimination success", OptSuccessFormula(),
                Blocks(Paragraph(
                    Text("The supremum of the equal-prior discrimination success "),
                    Ref(Optimality + ".isoSuccess"),
                    Text(" ranges over every global measurement of type "),
                    Ref(Measurement + ".LocalPOVM"),
                    Text(" with outcomes Fin n. The possible final states are given by "),
                    Ref(Optimality + ".fire"),
                    Text(". This is the success counterpart of the minimum-error objective P: "
                        + "problem-related.tex, lines 23–47, and searching.tex, lines 93–105. "
                        + "The definition permits every natural n and every amplitude function; "
                        + "normalization is imposed in the conjecture."))),
                AssessedProvenance.FromLiterature(Source)),
            Node("error-prob", "errorProb", "Minimum error objective", ErrorProbFormula(),
                Blocks(Paragraph(Text(
                    "The error objective is one minus optimal success. For a normalized probe this "
                    + "encodes P in problem-related.tex, lines 35–47; searching.tex, lines 100–105, "
                    + "writes the error as one minus the success of an optimal POVM. "
                    + "The formula itself is defined without a normalization hypothesis."))),
                AssessedProvenance.FromLiterature(Source)),
            Node("average", "average", "Coefficient-square average", AverageFormula(),
                Blocks(Paragraph(Text(
                    "At each Boolean word x, average takes the nonnegative real square root of "
                    + "the mean of the two squared complex amplitudes, then includes that real "
                    + "number in the complex scalars. This is the state in optimal.tex, line 144. "
                    + "It averages coefficient-squares and assigns nonnegative real amplitudes; "
                    + "it does not retain the phases of the two inputs."))),
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "claim", "The strict-averaging conjecture", ClaimFormula(),
                Blocks(Paragraph(Text(
                    "Conjecture 2, optimal.tex, lines 131–149, asserts that two normalized probes "
                    + "with unequal coefficient-squares somewhere and equal minimum error have "
                    + "an average with strictly smaller error. The unitary has eigenvalues "
                    + "exp(±iθ). Its angle range in problem-related.tex, lines 17–21, is expressed "
                    + "here in radians as 0 < θ < π. The statement quantifies over every natural "
                    + "sensor count n, every such angle θ, and every pair ψ, ψ′ of normalized "
                    + "complex amplitude functions on Fin n → Bool."))),
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Two distinct optimal probes prevent strict improvement"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For three sensors, take φ₁ and φ₂ to have amplitude 1/√3 on the words "
                        + "of weight one and two, respectively, and amplitude zero elsewhere. "
                        + "More generally, the uniform weight-l probe has squared amplitude "
                        + "1/(Nat.choose 3 l) on that weight class and zero outside it. "
                        + "This follows by squaring its real inverse square-root amplitude. "
                        + "The threshold T(3) is π/3: arccos(1/2) = π/3 and "
                        + "arccos(−1/2) = π − arccos(1/2). Thus θ = π/4 is positive and at most T(3).")),
                    Paragraph(Text(
                        "For the selected sensor positions 0 and 1, the agreement counts at "
                        + "weights 0, 1, 2, 3 are all one, and the disagreement counts are "
                        + "0, 2, 2, 0. The disagreement counting identity and the partition of "
                        + "each weight class give these values. Since cos(2θ) = 0, the overlap "
                        + "ratios are 1, 1/3, 1/3, 1. Both weights one and two therefore minimize "
                        + "the ratio. At the word whose only true coordinate is 0, the squared "
                        + "amplitudes of φ₁ and φ₂ are 1/3 and zero, so they differ.")),
                    Paragraph(Text(
                        "There is a three-outcome POVM with identity effect at outcome 0 and "
                        + "zero effects at the other outcomes.")),
                    Paragraph(Text("For any normalized probe, "),
                        Ref(Optimality + ".global_success_upper_bound"),
                        Text(" at n = 3 and θ = π/4 bounds every POVM success by "
                            + "d 3 (cstar 3 (π/4))². This bounds the range above without "
                            + "evaluating the bound.")),
                    Paragraph(Text("The "), Ref(Optimality + ".result"),
                        Text(" applies to each minimizing weight. For every normalized competitor "
                            + "ψ and every POVM M it supplies a POVM M′ on φ₁, and likewise on φ₂, "
                            + "whose success is at least that of ψ with M. The weight-class "
                            + "normalization theorem gives unit norm for both proposed probes. "
                            + "The nonempty POVM type and the upper bounds on success allow "
                            + "this comparison to pass to suprema: every normalized competitor "
                            + "has optimal success at most that of either φ₁ or φ₂.")),
                    Paragraph(Text(
                        "The average of any two normalized probes is normalized: its squared "
                        + "amplitude at x is exactly the mean of their squared amplitudes, "
                        + "because that mean is nonnegative; summing gives (1 + 1)/2 = 1. "
                        + "Applying the two optimal-success comparisons to φ₁ and φ₂ in both "
                        + "directions gives equal optimal successes and hence equal errors. "
                        + "Applying the comparison for φ₂ to their normalized average shows "
                        + "that the average has success at most that of φ₂, and thus error "
                        + "at least that of φ₂.")),
                    Paragraph(Text(
                        "Finally, π/4 < π, both probes are normalized, their coefficient-squares "
                        + "differ, and their errors agree. The conjecture would give an average "
                        + "error strictly smaller than the error of φ₂, contradicting the "
                        + "opposite weak inequality. This refutes the quantified strict-averaging statement."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhan-gupta-hillery-2024-detector-sensor-strict-averaging-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula,
        BlockSequence prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, prose, DescribeRole.Definition);

    private static Formula OptSuccessFormula() => All("n", Naturals(), All("θ", Reals(),
        All("ψ", State(), Equal(Typed(LocalCall("optSuccess", V("θ"), V("ψ")), Reals()),
            At(Qualified("iSup"), LambdaOf("M", Povm(),
                At(Owner("isoSuccess"), V("θ"), V("ψ"), V("M"))))))));

    private static Formula ErrorProbFormula() => All("n", Naturals(), All("θ", Reals(),
        All("ψ", State(), Equal(Typed(LocalCall("errorProb", V("θ"), V("ψ")), Reals()),
            Subtract(Typed(D(1), Reals()), LocalCall("optSuccess", V("θ"), V("ψ")))))));

    private static Formula AverageFormula() => All("n", Naturals(), All("ψ", State(),
        All("ψ'", State(), Equal(Typed(LocalCall("average", V("ψ"), V("ψ'")), State()),
            LambdaOf("x", Word(), At(Qualified("Complex", "ofReal"),
                At(Qualified("Real", "sqrt"), new Formula.Fraction(
                    Add(NormSq(At(V("ψ"), V("x"))), NormSq(At(V("ψ'"), V("x")))),
                    Typed(D(2), Reals())))))))));

    private static Formula ClaimFormula() => new Formula.Logic(
        Local("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody()));

    private static Formula ClaimBody()
    {
        Formula conclusion = Less(LocalCall("errorProb", V("θ"),
            LocalCall("average", V("ψ"), V("ψ'"))), LocalCall("errorProb", V("θ"), V("ψ'")));
        Formula sameError = Equal(LocalCall("errorProb", V("θ"), V("ψ")),
            LocalCall("errorProb", V("θ"), V("ψ'")));
        Formula different = Some("x", Word(), NotEqual(
            NormSq(At(V("ψ"), V("x"))), NormSq(At(V("ψ'"), V("x")))));
        Formula probes = All("ψ", State(), All("ψ'", State(),
            Arrow(Normalized(V("ψ")), Arrow(Normalized(V("ψ'")),
                Arrow(different, Arrow(sameError, conclusion))))));
        return All("n", Naturals(), All("θ", Reals(),
            Arrow(Less(Typed(D(0), Reals()), V("θ")),
                Arrow(Less(V("θ"), Qualified("Real", "pi")), probes))));
    }

    private static Formula Normalized(Formula ψ) => Equal(
        Seq(new Formula.Subscript(Sum, Seq(V("x"), Colon, Sp, Word())), Sp,
            Parenthesized(NormSq(At(ψ, V("x"))))), Typed(D(1), Reals()));
    private static Formula NormSq(Formula value) => At(Qualified("Complex", "normSq"), value);
    private static Formula Word() => new Formula.TypeArrow(At(Qualified("Fin"), V("n")), Qualified("Bool"));
    private static Formula State() => new Formula.TypeArrow(Parenthesized(Word()), Complexes());
    private static Formula Povm() => At(Qualified("D5", "S3", "Quantum", "Entanglement",
        "TriangleIndependentSourceNoise", "LocalPOVM"), Word(), At(Qualified("Fin"), V("n")));
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Measurements",
        "DetectorSensorStrictAveragingRefutation", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula Owner(string name) => Qualified("D5", "S3", "Quantum", "Measurement",
        "DetectorSensorDickeOptimality", name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(part switch
            {
                "D5" => Seq(F.Id("D"), D(5)),
                "S3" => Seq(F.Id("S"), D(3)),
                _ => F.Id(part),
            });
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula V(string name) => name switch
    {
        "θ" => Theta,
        "ψ" => Psi,
        "ψ'" => Seq(Psi, Apos),
        _ => F.Id(name),
    };
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula premise, Formula conclusion) =>
        new Formula.TypeArrow(Parenthesized(premise), Parenthesized(conclusion));
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
