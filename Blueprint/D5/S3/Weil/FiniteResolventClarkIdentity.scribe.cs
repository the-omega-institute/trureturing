using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class FiniteResolventClarkIdentityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/FiniteResolventClarkIdentity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite paired real spectrum becomes its exact resolvent-weighted atomic "
            + "circle measure under Cayley compactification.",
        H("Finite Resolvent--Clark Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("paired-ordinate-measure"),
                DeclarationHandle.Create(Prefix + "pairedOrdinateMeasure"),
                H("Paired ordinate measure"),
                StatementSource.FromAuthor(PairedMeasureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each finite index contributes equally weighted Dirac atoms at its "
                        + "positive and negative real ordinates. The measure sum retains "
                        + "multiplicity when ordinates coincide."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-atomic-clark-measure"),
                DeclarationHandle.Create(Prefix + "finiteAtomicClarkMeasure"),
                H("Finite atomic circle measure"),
                StatementSource.FromAuthor(AtomicClarkFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every paired atom is moved by the canonical Cayley map and its mass "
                        + "is multiplied by the exact reciprocal-quadratic resolvent "
                        + "density. Evenness of that density gives both signs the same "
                        + "coefficient."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-atomic-cayley-pushforward"),
                DeclarationHandle.Create(Prefix + "finite_atomic_cayley_pushforward"),
                H("Finite atomic Cayley pushforward"),
                StatementSource.FromAuthor(PushforwardFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Mathlib distributes withDensity and Measure.map across the finite "
                            + "measure sum, scalar multiplication, and each paired sum.")),
                    Paragraph(Text(
                        "The Dirac with-density and map laws then evaluate every summand. "
                            + "This is the nontrivial finite atomic calculation on which the "
                            + "final identity rests."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-resolvent-clark-identity"),
                DeclarationHandle.Create(Prefix + "finite_resolvent_clark_identity"),
                H("Half-scale resolvent--Clark identity"),
                StatementSource.FromAuthor(ClarkIdentityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At scale one half, the compactification is the explicit finite "
                            + "atomic Li measure by the preceding pushforward theorem.")),
                    Paragraph(Text(
                        "The supplied Clark measure is required to have that same atomic "
                            + "expansion. This premise records the analytic Clark/Herglotz "
                            + "identification that is not available in the repository, so "
                            + "the theorem does not overclaim an unconditional equality."))),
                DescribeRole.Theorem))));

    private static Formula PairedMeasureFormula()
    {
        Formula jType = F.Id("J");
        Formula mass = F.Id("m");
        Formula ordinate = F.Id("gamma");
        Formula j = F.Id("j");
        Formula gammaJ = Apply(ordinate, j);
        Formula atomPair = Add(Call("dirac", gammaJ), Call("dirac", Negate(gammaJ)));
        Formula summand = Mul(Apply(mass, j), atomPair);
        Formula statement = Equal(
            Call("pairedOrdinateMeasure", mass, ordinate),
            Call("sum", j, jType, summand));
        return Disp(FiniteSpectrumBinders(statement));
    }

    private static Formula AtomicClarkFormula()
    {
        Formula jType = F.Id("J");
        Formula a = F.Id("a");
        Formula mass = F.Id("m");
        Formula ordinate = F.Id("gamma");
        Formula j = F.Id("j");
        Formula gammaJ = Apply(ordinate, j);
        Formula density = Call("resolventDensity", a, gammaJ);
        Formula atomPair = Add(
            Call("dirac", Call("cayleyCircle", a, gammaJ)),
            Call("dirac", Call("cayleyCircle", a, Negate(gammaJ))));
        Formula summand = Mul(Mul(Apply(mass, j), density), atomPair);
        Formula statement = Equal(
            Call("finiteAtomicClarkMeasure", a, mass, ordinate),
            Call("sum", j, jType, summand));
        return Disp(PositiveScaleBinders(statement));
    }

    private static Formula PushforwardFormula()
    {
        Formula a = F.Id("a");
        Formula mass = F.Id("m");
        Formula ordinate = F.Id("gamma");
        Formula statement = Equal(
            Call("cayleyCompactification", a,
                Call("pairedOrdinateMeasure", mass, ordinate)),
            Call("finiteAtomicClarkMeasure", a, mass, ordinate));
        return Disp(PositiveScaleBinders(statement));
    }

    private static Formula ClarkIdentityFormula()
    {
        Formula mass = F.Id("m");
        Formula ordinate = F.Id("gamma");
        Formula clark = F.Id("sigma");
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula atomic = Call("finiteAtomicClarkMeasure", half, mass, ordinate);
        Formula resolvent = Call("cayleyCompactification", half,
            Call("pairedOrdinateMeasure", mass, ordinate));
        Formula premise = Equal(clark, atomic);
        Formula conclusion = And(Equal(resolvent, atomic), Equal(atomic, clark));
        Formula body = Implies(premise, conclusion);
        return Disp(ForAll(
            [
                Bound("J", F.Id("Type")),
                Bound("m", Arrow(F.Id("J"), F.Id("ENNReal"))),
                Bound("gamma", Arrow(F.Id("J"), RealType())),
                Bound("sigma", Call("Measure", F.Id("Circle"))),
            ],
            Implies(Call("Fintype", F.Id("J")), body)));
    }

    private static Formula FiniteSpectrumBinders(Formula body) =>
        ForAll(
            [
                Bound("J", F.Id("Type")),
                Bound("m", Arrow(F.Id("J"), F.Id("ENNReal"))),
                Bound("gamma", Arrow(F.Id("J"), RealType())),
            ],
            Implies(Call("Fintype", F.Id("J")), body));

    private static Formula PositiveScaleBinders(Formula body) =>
        ForAll(
            [
                Bound("J", F.Id("Type")),
                Bound("a", RealType()),
                Bound("m", Arrow(F.Id("J"), F.Id("ENNReal"))),
                Bound("gamma", Arrow(F.Id("J"), RealType())),
            ],
            Implies(
                And(Call("Fintype", F.Id("J")), Less(D(0), F.Id("a"))),
                body));

    private static Formula Negate(Formula value) => Seq(Minus, value);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula RealType() => Call("Real");
}
