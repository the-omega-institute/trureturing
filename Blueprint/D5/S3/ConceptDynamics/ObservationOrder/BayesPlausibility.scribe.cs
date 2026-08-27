using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationOrder;

internal sealed class BayesPlausibilityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ObservationOrder/BayesPlausibility."
            + "bayes_plausibility";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite posterior mixtures reconstruct their prior distribution.",
        H("Bayes Plausibility"),
        Blocks(Describe.Lean(
            DescribeId.Create("bayes-plausibility"),
            DeclarationHandle.Create(Declaration),
            H("The posterior mixture is the prior"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A finite world PMF and a PMF-valued finite signal kernel construct "
                        + "the displayed real joint law. Its canonical first marginal is "
                        + "the signal weight, and its canonical conditional is the posterior.")),
                Paragraph(Text(
                    "On a positive-weight signal fiber, multiplying the conditional by its "
                        + "marginal recovers the joint mass. On a zero-weight fiber, "
                        + "nonnegativity forces every joint mass in that fiber to vanish.")),
                Paragraph(Text(
                    "Summing the recovered joint masses over signals leaves the prior mass "
                        + "times the normalized signal-kernel mass. This proves both the "
                        + "function equality and its public pointwise form.")),
                Paragraph(Text(
                    "Repository and pinned-library searches found no exact theorem on this "
                        + "finite PMF/kernel carrier. The proof imports the existing marginal "
                        + "and conditional primitives and applies Mathlib's PMF normalization."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula worldType = F.Id("World");
        Formula signalType = F.Id("Signal");
        Formula world = F.Id("omega");
        Formula signal = F.Id("s");
        Formula prior = F.Id("mu");
        Formula kernel = F.Id("K");
        Formula joint = F.Id("jointLaw");
        Formula weight = F.Id("lambda");
        Formula posterior = F.Id("posterior");
        Formula reals = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula jointType = Arrow(
            F.Seq(signalType, F.Sp, F.Times, F.Sp, worldType), reals);
        Formula weightType = Arrow(signalType, reals);
        Formula posteriorType = Arrow(signalType, Arrow(worldType, reals));
        Formula priorAtWorld = Apply(prior, world);
        Formula kernelAt = Apply(Apply(kernel, world), signal);
        Formula jointAt = ApplyMany(joint, signal, world);
        Formula weightAt = Apply(weight, signal);
        Formula posteriorAt = ApplyMany(posterior, signal, world);
        Formula jointLet = F.Seq(
            F.Operatorname, F.Grp(F.Id("let")), F.Sp, joint,
            F.Sp, F.Colon, F.Sp, jointType, F.Sp, F.Colon, F.Eq, F.Sp,
            F.Open, signal, F.Comma, world, F.Close, F.Sp, F.Mapsto, F.Sp,
            Multiply(Call("toReal", priorAtWorld), Call("toReal", kernelAt)),
            F.Semi, F.RowBreak, F.Grp());
        Formula weightLet = F.Seq(
            F.Operatorname, F.Grp(F.Id("let")), F.Sp, weight,
            F.Sp, F.Colon, F.Sp, weightType, F.Sp, F.Colon, F.Eq, F.Sp,
            signal, F.Sp, F.Mapsto, F.Sp,
            Call("marginal", joint, signal), F.Semi, F.RowBreak, F.Grp());
        Formula posteriorLet = F.Seq(
            F.Operatorname, F.Grp(F.Id("let")), F.Sp, posterior,
            F.Sp, F.Colon, F.Sp, posteriorType, F.Sp, F.Colon, F.Eq, F.Sp,
            F.Open, signal, F.Comma, world, F.Close, F.Sp, F.Mapsto, F.Sp,
            Call("conditional", joint, signal, world), F.Semi, F.RowBreak, F.Grp());
        Formula posteriorMixture = F.Seq(
            F.Sum, F.Underscore, F.Grp(signal, F.Sp, F.InMacro, F.Sp, signalType), F.Sp,
            Multiply(weightAt, posteriorAt));
        Formula priorReal = Call("toReal", priorAtWorld);
        Formula functionEquality = Relation(
            F.Seq(F.Open, world, F.Sp, F.Mapsto, F.Sp, posteriorMixture, F.Close),
            FormulaRelationOperator.Equal,
            F.Seq(F.Open, world, F.Sp, F.Mapsto, F.Sp, priorReal, F.Close));
        Formula pointwiseEquality = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("omega"),
            worldType,
            Relation(posteriorMixture, FormulaRelationOperator.Equal, priorReal));
        Formula carriers = And(
            Call("Fintype", worldType),
            Call("Fintype", signalType));
        Formula inputs = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("mu", Call("PMF", worldType)),
                Bound("K", Arrow(worldType, Call("PMF", signalType))),
            ],
            F.Seq(
                jointLet,
                weightLet,
                posteriorLet,
                Logic(functionEquality, FormulaLogicOperator.And, pointwiseEquality)));

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

    private static Formula Logic(
        Formula left,
        FormulaLogicOperator operation,
        Formula right) => new Formula.Logic(left, operation, right);

    private static Formula And(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        Logic(premise, FormulaLogicOperator.Implies, conclusion);
}
