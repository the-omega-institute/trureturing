using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MeasureSeparation;

internal sealed class SingularPosteriorCollapseDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Singular transcript laws make binary posteriors collapse under generated information.",
        H("Posterior Collapse under Singular Laws"),
        Blocks(
            Definition(
                "binary-prior-mixture-definition",
                "binaryPriorMixture",
                "Binary prior mixture",
                BinaryPriorMixtureFormula(),
                "The prior weights the two transcript laws, including totalized endpoints."),
            Definition(
                "likelihood-posterior-definition",
                "likelihoodPosterior",
                "Likelihood posterior",
                LikelihoodPosteriorFormula(),
                "This is the exact binary likelihood normalization displayed in section 225."),
            Definition(
                "likelihood-posterior-process-definition",
                "likelihoodPosteriorProcess",
                "Likelihood posterior process",
                LikelihoodPosteriorProcessFormula(),
                "The likelihood posterior is evaluated at every natural observation time."),
            Definition(
                "binary-posterior-process-definition",
                "binaryPosteriorProcess",
                "Conditional posterior process",
                BinaryPosteriorProcessFormula(),
                "The posterior is the conditional expectation of a separating-event indicator."),
            Theorem(
                "mutually-singular-laws-have-collapsing-posterior",
                "mutually_singular_laws_have_collapsing_posterior",
                "Singular laws have collapsing posterior",
                CollapseFormula(),
                "A perfect separator and conditional-expectation convergence give limits one "
                    + "and zero under the two laws."),
            Theorem(
                "zero-prior-is-necessary",
                "zero_prior_is_necessary",
                "A zero prior prevents first-state completion",
                ZeroPriorFormula(),
                "With constant unit likelihood, the posterior remains zero."),
            Theorem(
                "one-prior-is-necessary",
                "one_prior_is_necessary",
                "A unit prior prevents second-state completion",
                OnePriorFormula(),
                "With constant unit likelihood, the posterior remains one."),
            Theorem(
                "equal-law-is-not-perfectly-separable",
                "equal_law_is_not_perfectly_separable",
                "Equal laws have no perfect separator",
                EqualLawFormula(),
                "One Dirac law cannot assign both full and zero mass to the same event."),
            Theorem(
                "empty-transcript-has-no-probability-law",
                "empty_transcript_has_no_probability_law",
                "The empty transcript type has no probability law",
                EmptyTranscriptFormula(),
                "Probability normalization forces the sample type to be nonempty."),
            Theorem(
                "unit-probability-laws-are-equal",
                "unit_probability_laws_are_equal",
                "Singleton probability laws coincide",
                UnitLawFormula(),
                "Every measurable singleton event is either empty or universal."),
            Theorem(
                "trivial-filtration-does-not-generate-bool",
                "trivial_filtration_does_not_generate_bool",
                "The bottom Boolean filtration is not generating",
                TrivialFiltrationFormula(),
                "A constant bottom filtration never reveals the nontrivial Boolean event."),
            Theorem(
                "filtration-generation-is-necessary",
                "filtration_generation_is_necessary",
                "Generation is necessary for posterior collapse",
                GenerationNecessaryFormula(),
                "Singular Boolean Dirac laws with half prior retain posterior one half under "
                    + "the bottom filtration."))));

    private static DocumentBlock Definition(
        string id,
        string declaration,
        string title,
        Formula statement,
        string explanation) =>
        Describe.Lean(
            DescribeId.Create(id),
            Handle(declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            DescribeRole.Definition);

    private static DocumentBlock Theorem(
        string id,
        string declaration,
        string title,
        Formula statement,
        string explanation) =>
        Describe.Lean(
            DescribeId.Create(id),
            Handle(declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            DescribeRole.Theorem);

    private static Formula BinaryPriorMixtureFormula() =>
        Disp(Equal(
            Call("binaryPriorMixture", F.Id("a"), F.Id("Px"), F.Id("Py")),
            Add(
                Multiply(Call("ofReal", F.Id("a")), F.Id("Px")),
                Multiply(
                    Call("ofReal", Subtract(D(1), F.Id("a"))),
                    F.Id("Py")))));

    private static Formula LikelihoodPosteriorFormula() =>
        Disp(Equal(
            Call("likelihoodPosterior", F.Id("a"), F.Id("L")),
            Divide(
                Multiply(F.Id("a"), F.Id("L")),
                Add(Multiply(F.Id("a"), F.Id("L")), Subtract(D(1), F.Id("a"))))));

    private static Formula LikelihoodPosteriorProcessFormula() =>
        Disp(Equal(
            Call("likelihoodPosteriorProcess", F.Id("a"), F.Id("L"), F.Id("m"),
                F.Id("omega")),
            Call("likelihoodPosterior", F.Id("a"),
                Call("L", F.Id("m"), F.Id("omega")))));

    private static Formula BinaryPosteriorProcessFormula() =>
        Disp(Equal(
            Call("binaryPosteriorProcess", F.Id("M"), F.Id("F"), F.Id("A"),
                F.Id("m"), F.Id("omega")),
            Call("conditionalExpectation", F.Id("M"), Call("indicator", F.Id("A")),
                Call("F", F.Id("m")), F.Id("omega"))));

    private static Formula CollapseFormula() =>
        Disp(new Formula.Logic(
            And(
                Call("InteriorPrior", F.Id("a")),
                And(
                    Call("Generates", F.Id("F")),
                    Call("MutuallySingular", F.Id("Px"), F.Id("Py")))),
            FormulaLogicOperator.Implies,
            Call("ExistsPerfectSeparatorWithPosteriorLimits", F.Id("Px"),
                F.Id("Py"), F.Id("a"), F.Id("F"), D(1), D(0))));

    private static Formula ZeroPriorFormula() =>
        Disp(Not(Call("Tendsto", Call("constantLikelihoodPosterior", D(0)), D(1))));

    private static Formula OnePriorFormula() =>
        Disp(Not(Call("Tendsto", Call("constantLikelihoodPosterior", D(1)), D(0))));

    private static Formula EqualLawFormula() =>
        Disp(Not(Call("ExistsPerfectSeparator", Call("dirac", F.Id("unit")),
            Call("dirac", F.Id("unit")))));

    private static Formula EmptyTranscriptFormula() =>
        Disp(Not(Call("ExistsProbabilityMeasure", Emptyset)));

    private static Formula UnitLawFormula() =>
        Disp(Call("AllProbabilityMeasuresEqual", F.Id("Unit")));

    private static Formula TrivialFiltrationFormula() =>
        Disp(NotEqual(
            Call("join", Call("constantBottomFiltration", F.Id("Bool"))),
            Call("fullMeasurableSpace", F.Id("Bool"))));

    private static Formula GenerationNecessaryFormula() =>
        Disp(And(
            Call("MutuallySingular", Call("dirac", F.Id("true")),
                Call("dirac", F.Id("false"))),
            Not(Call("TendstoUnder", Call("dirac", F.Id("true")),
                Call("bottomFiltrationPosterior", Divide(D(1), D(2))), D(1)))));

    private static DeclarationHandle Handle(string declaration) =>
        DeclarationHandle.Create(Prefix + declaration);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Divide(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Not(Formula statement) =>
        Seq(Neg, Sp, statement);
}
