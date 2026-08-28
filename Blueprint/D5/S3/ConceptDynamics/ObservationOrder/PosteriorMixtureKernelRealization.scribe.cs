using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationOrder;

internal sealed class PosteriorMixtureKernelRealizationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ObservationOrder/PosteriorMixtureKernelRealization."
            + "posterior_mixture_kernel_realization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Bayes-plausible finite posterior mixture is realized by its canonical signal kernel.",
        H("Posterior Mixture Kernel Realization"),
        Blocks(Describe.Lean(
            DescribeId.Create("posterior-mixture-kernel-realization"),
            DeclarationHandle.Create(Declaration),
            H("Bayes-plausible posterior mixtures are realizable"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The prior, every prescribed posterior, and the signal weights are finite "
                        + "PMFs. Thus the nonnegativity and unit-mass requirements on the "
                        + "posterior family and weights are part of their public carriers.")),
                Paragraph(Text(
                    "The theorem exposes the canonical signal kernel as the prescribed signal "
                        + "weight times posterior mass, divided by the positive prior mass. "
                        + "The accompanying joint law is induced from that kernel and prior.")),
                Paragraph(Text(
                    "The posterior-mixture equation normalizes the kernel at every world. "
                        + "Posterior normalization gives the prescribed signal marginal, and "
                        + "division by a positive signal weight recovers its posterior.")),
                Paragraph(Text(
                    "The imported forward plausibility theorem uses the same canonical marginal "
                        + "and conditional operations. Repository search found no prior reverse "
                        + "realization theorem containing all displayed clauses."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula worldType = F.Id("World");
        Formula signalType = F.Id("Signal");
        Formula world = F.Id("omega");
        Formula signal = F.Id("s");
        Formula prior = F.Id("mu");
        Formula posterior = F.Id("muPost");
        Formula weight = F.Id("lambda");
        Formula kernel = F.Id("kappa");
        Formula joint = F.Id("jointLaw");
        Formula reals = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula priorAt = Apply(prior, world);
        Formula posteriorAt = ApplyMany(posterior, signal, world);
        Formula weightAt = Apply(weight, signal);
        Formula priorReal = Call("toReal", priorAt);
        Formula posteriorReal = Call("toReal", posteriorAt);
        Formula weightReal = Call("toReal", weightAt);
        Formula kernelAt = ApplyMany(kernel, world, signal);
        Formula jointAt = ApplyMany(joint, signal, world);
        Formula weightedPosterior = Multiply(weightReal, posteriorReal);
        Formula kernelBody = new Formula.Fraction(weightedPosterior, priorReal);
        Formula posteriorFamilyType = Arrow(signalType, Call("PMF", worldType));
        Formula kernelType = Arrow(worldType, Arrow(signalType, reals));
        Formula jointType = Arrow(
            F.Seq(signalType, F.Sp, F.Times, F.Sp, worldType), reals);
        Formula priorPositive = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("omega"),
            worldType,
            Relation(Num(0), FormulaRelationOperator.LessThan, priorReal));
        Formula posteriorMixture = F.Seq(
            F.Sum, F.Underscore, F.Grp(signal, F.Sp, F.InMacro, F.Sp, signalType),
            F.Sp, weightedPosterior);
        Formula mixturePremise = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("omega"),
            worldType,
            Relation(posteriorMixture, FormulaRelationOperator.Equal, priorReal));
        Formula kernelLet = F.Seq(
            F.Operatorname, F.Grp(F.Id("let")), F.Sp, kernel,
            F.Sp, F.Colon, F.Sp, kernelType, F.Sp, F.Colon, F.Eq, F.Sp,
            F.Open, world, F.Comma, signal, F.Close, F.Sp, F.Mapsto, F.Sp,
            kernelBody, F.Semi, F.Sp);
        Formula jointLet = F.Seq(
            F.Operatorname, F.Grp(F.Id("let")), F.Sp, joint,
            F.Sp, F.Colon, F.Sp, jointType, F.Sp, F.Colon, F.Eq, F.Sp,
            F.Open, signal, F.Comma, world, F.Close, F.Sp, F.Mapsto, F.Sp,
            Multiply(priorReal, kernelAt), F.Semi, F.Sp);
        Formula kernelNonnegative = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("omega", worldType), Bound("s", signalType)],
            Relation(Num(0), FormulaRelationOperator.LessThanOrEqual, kernelAt));
        Formula kernelNormalized = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("omega"),
            worldType,
            Relation(
                F.Seq(
                    F.Sum, F.Underscore,
                    F.Grp(signal, F.Sp, F.InMacro, F.Sp, signalType),
                    F.Sp, kernelAt),
                FormulaRelationOperator.Equal,
                Num(1)));
        Formula signalMarginal = Relation(
            Call("marginal", joint),
            FormulaRelationOperator.Equal,
            F.Seq(F.Open, signal, F.Sp, F.Mapsto, F.Sp, weightReal, F.Close));
        Formula recovery = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("s"),
            signalType,
            Implies(
                Relation(Num(0), FormulaRelationOperator.LessThan, weightReal),
                Relation(
                    Call("conditional", joint, signal),
                    FormulaRelationOperator.Equal,
                    F.Seq(F.Open, world, F.Sp, F.Mapsto, F.Sp, posteriorReal, F.Close))));
        Formula conclusions = And(
            kernelNonnegative,
            And(kernelNormalized, And(signalMarginal, recovery)));
        Formula inputs = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("mu", Call("PMF", worldType)),
                Bound("muPost", posteriorFamilyType),
                Bound("lambda", Call("PMF", signalType)),
            ],
            Implies(
                priorPositive,
                Implies(mixturePremise, F.Seq(kernelLet, jointLet, conclusions))));
        Formula carriers = And(
            Call("Fintype", worldType),
            Call("Fintype", signalType));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("World", type), Bound("Signal", type)],
            Implies(carriers, inputs)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula ApplyMany(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Relation(
        Formula left,
        FormulaRelationOperator operation,
        Formula right) => new Formula.Relation(left, operation, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
}
