using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MeasureSeparation;

internal sealed class FactorizedTranscriptKernelBarrierDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Factorized transcript laws and every finite repetition agree on interface fibers.",
        H("Factorized Transcript Kernel Barrier"),
        Blocks(
            Definition(
                "transcript-kernel-definition",
                "TranscriptKernel",
                "Transcript kernels",
                "A transcript kernel is a state-indexed family of probability laws. The state "
                    + "needs no measurable structure because the source imposes none."),
            Definition(
                "kernel-factors-through-definition",
                "KernelFactorsThrough",
                "Factorization through an interface",
                "The law family factors when it is the composite of the interface with a "
                    + "probability-law family on the interface codomain."),
            Definition(
                "repeated-transcript-kernel-definition",
                "RepeatedTranscriptKernel",
                "Repeated transcript kernels",
                "A length-n transcript kernel returns a joint probability law on Fin n "
                    + "coordinates, so correlated repetitions are included."),
            Definition(
                "iid-repetition-definition",
                "iidRepetition",
                "Independent repetition",
                "The canonical finite product of one state-conditioned law gives every iid "
                    + "sample size, including the empty product."),
            Definition(
                "identifies-target-definition",
                "IdentifiesTarget",
                "Exact law identification",
                "Exact law identification requires the target to agree whenever the complete "
                    + "transcript laws agree."),
            Theorem(
                "factorized-transcript-kernel-eq-on-fiber",
                "factorized_transcript_kernel_eq_on_fiber",
                "Factorized laws agree on interface fibers",
                FiberEqualityFormula(),
                "Substituting the named factorization turns equal interface values into equal "
                    + "arguments of the reduced law family."),
            Theorem(
                "iid-repetition-preserves-factorization",
                "iid_repetition_preserves_factorization",
                "Independent repetition preserves factorization",
                IidFactorizationFormula(),
                "Apply the finite probability-product constructor to the reduced law family. "
                    + "The construction works uniformly at every natural sample count."),
            Theorem(
                "factorized-repeated-kernel-eq-on-fiber",
                "factorized_repeated_kernel_eq_on_fiber",
                "Correlated repeated laws agree on fibers",
                RepeatedEqualityFormula(),
                "No coordinate independence is used: equality follows from factorization of "
                    + "the whole joint transcript law."),
            Theorem(
                "factorized-repeated-kernel-cannot-identify-fiber-varying-target",
                "factorized_repeated_kernel_cannot_identify_fiber_varying_target",
                "Repeated laws cannot identify a fiber-varying target",
                NonidentificationFormula(),
                "Two same-fiber states have the same joint transcript law. If their target "
                    + "values differ, exact identification contradicts that equality."),
            Definition(
                "boolean-interface-definition",
                "booleanInterface",
                "The constant Boolean interface",
                "The concrete interface sends both Boolean states to the sole Unit value."),
            Definition(
                "boolean-target-definition",
                "booleanTarget",
                "The varying Boolean target",
                "The concrete target is the Boolean identity and therefore varies in the one "
                    + "interface fiber."),
            Definition(
                "constant-boolean-transcript-kernel-definition",
                "constantBooleanTranscriptKernel",
                "The constant point-mass transcript law",
                "At either Boolean state, the observation law is the point mass on Unit."),
            Definition(
                "distinguishing-boolean-transcript-kernel-definition",
                "distinguishingBooleanTranscriptKernel",
                "The state-recording point-mass law",
                "This audit kernel assigns each Boolean state its own Dirac probability law."),
            Theorem(
                "boolean-target-not-identified-by-any-iid-repetition",
                "boolean_target_not_identified_by_any_iid_repetition",
                "No finite repetition identifies the Boolean target",
                BooleanCounterexampleFormula(),
                "For every n, the iid product remains constant on the two Boolean states while "
                    + "the identity target separates them. This explicitly includes n equal to "
                    + "zero."),
            Theorem(
                "transcript-factorization-is-necessary",
                "transcript_factorization_is_necessary",
                "Factorization cannot be deleted",
                FactorizationNecessaryFormula(),
                "With the constant interface, distinct Boolean Dirac laws violate the fiber "
                    + "conclusion and cannot factor through that interface."),
            Theorem(
                "same-fiber-is-necessary",
                "same_fiber_is_necessary",
                "The same-fiber premise cannot be deleted",
                SameFiberNecessaryFormula(),
                "The identity interface admits the state-recording Dirac law as a factorized "
                    + "kernel, but its two different fibers have unequal laws."),
            Theorem(
                "fiber-variation-is-necessary-for-nonidentification",
                "fiber_variation_is_necessary_for_nonidentification",
                "Target variation is required for nonidentification",
                VariationNecessaryFormula(),
                "A constant Unit-valued target is identified under every iid repetition of the "
                    + "constant factorized kernel."))));

    private static DocumentBlock Definition(
        string id,
        string declaration,
        string title,
        string explanation) =>
        Describe.Lean(
            DescribeId.Create(id),
            Handle(declaration),
            H(title),
            StatementSource.WithoutFormula(),
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

    private static Formula FiberEqualityFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula q = F.Id("q");
        Formula kernel = F.Id("K");
        Formula premise = And(
            Factors(q, kernel),
            Equal(Apply(q, x), Apply(q, y)));
        return QuantifiedKernelFormula(
            kernel,
            q,
            x,
            y,
            Implies(premise, Equal(Apply(kernel, x), Apply(kernel, y))));
    }

    private static Formula IidFactorizationFormula()
    {
        Formula state = F.Id("X");
        Formula basis = F.Id("B");
        Formula output = F.Id("Y");
        Formula q = F.Id("q");
        Formula kernel = F.Id("K");
        Formula n = F.Id("n");
        Formula body = Implies(
            Factors(q, kernel),
            Factors(q, Iid(n, kernel)));
        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", Type()),
                Bound("B", Type()),
                Bound("Y", Type()),
                Bound("q", Arrow(state, basis)),
                Bound("K", KernelType(state, output)),
                Bound("n", Call("Nat")),
            ],
            body));
    }

    private static Formula RepeatedEqualityFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula q = F.Id("q");
        Formula repeated = F.Id("Kn");
        Formula premise = And(
            Factors(q, repeated),
            Equal(Apply(q, x), Apply(q, y)));
        return QuantifiedRepeatedFormula(
            repeated,
            q,
            x,
            y,
            Implies(premise, Equal(Apply(repeated, x), Apply(repeated, y))));
    }

    private static Formula NonidentificationFormula()
    {
        Formula state = F.Id("X");
        Formula basis = F.Id("B");
        Formula output = F.Id("Y");
        Formula targetType = F.Id("A");
        Formula n = F.Id("n");
        Formula q = F.Id("q");
        Formula repeated = F.Id("Kn");
        Formula target = F.Id("T");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula premises = And(
            Factors(q, repeated),
            And(
                Equal(Apply(q, x), Apply(q, y)),
                NotEqual(Apply(target, x), Apply(target, y))));
        Formula conclusion = new Formula.Not(
            Call("IdentifiesTarget", repeated, target));
        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", Type()),
                Bound("B", Type()),
                Bound("Y", Type()),
                Bound("A", Type()),
                Bound("n", Call("Nat")),
                Bound("q", Arrow(state, basis)),
                Bound("Kn", RepeatedType(n, state, output)),
                Bound("T", Arrow(state, targetType)),
                Bound("x", state),
                Bound("y", state),
            ],
            Implies(premises, conclusion)));
    }

    private static Formula BooleanCounterexampleFormula()
    {
        Formula n = F.Id("n");
        Formula repeated = Iid(n, F.Id("constantBooleanTranscriptKernel"));
        Formula conclusion = new Formula.Not(
            Call("IdentifiesTarget", repeated, F.Id("booleanTarget")));
        return F.Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            Call("Nat"),
            conclusion));
    }

    private static Formula FactorizationNecessaryFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula q = F.Id("q");
        Formula kernel = F.Id("K");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula witness = And(
            Equal(Apply(q, x), Apply(q, y)),
            And(
                NotEqual(Apply(kernel, x), Apply(kernel, y)),
                new Formula.Not(Factors(q, kernel))));
        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("q", Arrow(boolean, unit)),
                Bound("K", KernelType(boolean, boolean)),
                Bound("x", boolean),
                Bound("y", boolean),
            ],
            witness));
    }

    private static Formula SameFiberNecessaryFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula q = F.Id("q");
        Formula kernel = F.Id("K");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula witness = And(
            Factors(q, kernel),
            And(
                NotEqual(Apply(q, x), Apply(q, y)),
                NotEqual(Apply(kernel, x), Apply(kernel, y))));
        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("q", Arrow(boolean, boolean)),
                Bound("K", KernelType(boolean, boolean)),
                Bound("x", boolean),
                Bound("y", boolean),
            ],
            witness));
    }

    private static Formula VariationNecessaryFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula q = F.Id("q");
        Formula kernel = F.Id("K");
        Formula target = F.Id("T");
        Formula n = F.Id("n");
        Formula allSamples = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            Call("Nat"),
            Call("IdentifiesTarget", Iid(n, kernel), target));
        Formula witness = And(Factors(q, kernel), allSamples);
        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("q", Arrow(boolean, unit)),
                Bound("K", KernelType(boolean, unit)),
                Bound("T", Arrow(boolean, unit)),
            ],
            witness));
    }

    private static Formula QuantifiedKernelFormula(
        Formula kernel,
        Formula q,
        Formula x,
        Formula y,
        Formula body)
    {
        Formula state = F.Id("X");
        Formula basis = F.Id("B");
        Formula output = F.Id("Y");
        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", Type()),
                Bound("B", Type()),
                Bound("Y", Type()),
                Bound("q", Arrow(state, basis)),
                Bound("K", KernelType(state, output)),
                Bound("x", state),
                Bound("y", state),
            ],
            body));
    }

    private static Formula QuantifiedRepeatedFormula(
        Formula repeated,
        Formula q,
        Formula x,
        Formula y,
        Formula body)
    {
        Formula state = F.Id("X");
        Formula basis = F.Id("B");
        Formula output = F.Id("Y");
        Formula n = F.Id("n");
        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", Type()),
                Bound("B", Type()),
                Bound("Y", Type()),
                Bound("n", Call("Nat")),
                Bound("q", Arrow(state, basis)),
                Bound("Kn", RepeatedType(n, state, output)),
                Bound("x", state),
                Bound("y", state),
            ],
            body));
    }

    private static DeclarationHandle Handle(string declaration) =>
        DeclarationHandle.Create(Prefix + declaration);

    private static Formula Type() => Call("Type");

    private static Formula KernelType(Formula state, Formula output) =>
        Arrow(state, Call("ProbabilityMeasure", output));

    private static Formula RepeatedType(Formula n, Formula state, Formula output) =>
        KernelType(state, Arrow(Call("Fin", n), output));

    private static Formula Factors(Formula q, Formula kernel) =>
        Call("KernelFactorsThrough", q, kernel);

    private static Formula Iid(Formula n, Formula kernel) =>
        Call("iidRepetition", n, kernel);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
