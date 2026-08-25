using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class StochasticDescentEquivalenceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/DecisionRisk/StochasticDescentEquivalence."
            + "stochastic_descent_equivalence";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A discrete transition law descends to the effective readout image exactly when "
            + "its observed rows are constant on readout fibers.",
        H("Stochastic Descent Equivalence"),
        Blocks(Describe.Lean(
            DescribeId.Create("stochastic-descent-equivalence"),
            DeclarationHandle.Create(Declaration),
            H("Stochastic descent is equivalent to strong lumpability"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The source transition assigns a probability mass function on the state "
                        + "space to every current state. Mapping that law through q gives the "
                        + "one-step observed law.")),
                Paragraph(Text(
                    "The first clause constructs a transition law on the literal effective "
                        + "image of q. Its pushforward along the subtype inclusion recovers "
                        + "every one-step observed law.")),
                Paragraph(Text(
                    "The second clause is strong lumpability: states in one q-fiber have equal "
                        + "observed rows. The third clause factors those rows through the "
                        + "current effective readout without yet requiring an image-valued "
                        + "next state.")),
                Paragraph(Text(
                    "Canonical range factorization and range splitting construct the descended "
                        + "transition. No finiteness or nonemptiness assumption is needed."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula state = F.Id("X");
        Formula readoutType = F.Id("B");
        Formula readout = F.Id("q");
        Formula transition = F.Id("K");
        Formula quotientKernel = F.Id("Kbar");
        Formula observedTransition = F.Id("L");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula effectiveImage = Call("range", readout);
        Formula stateLaw = Call("PMF", state);
        Formula imageLaw = Call("PMF", effectiveImage);
        Formula readoutLaw = Call("PMF", readoutType);
        Formula currentImageX = Call("rangeFactorization", readout, x);
        Formula currentImageY = Call("rangeFactorization", readout, y);
        Formula observedLawX = Call("map", Apply(transition, x), readout);
        Formula observedLawY = Call("map", Apply(transition, y), readout);
        Formula quotientLaw = Call(
            "map", Apply(quotientKernel, currentImageX), F.Id("val"));
        Formula descentClause = Seq(
            Exists, Sp,
            Typed(quotientKernel, Arrow(effectiveImage, imageLaw)), Comma,
            RowBreak, Grp(),
            Forall, Sp, Typed(x, state), Comma, Sp,
            observedLawX, Sp, Eq, Sp, quotientLaw);
        Formula lumpabilityClause = Seq(
            Forall, Sp, Typed(x, state), Comma, Sp, Typed(y, state), Comma, Sp,
            Apply(readout, x), Sp, Eq, Sp, Apply(readout, y), Sp,
            Rightarrow, Sp, observedLawX, Sp, Eq, Sp, observedLawY);
        Formula factorizationClause = Seq(
            Exists, Sp,
            Typed(observedTransition, Arrow(effectiveImage, readoutLaw)), Comma,
            RowBreak, Grp(),
            Forall, Sp, Typed(x, state), Comma, Sp,
            observedLawX, Sp, Eq, Sp,
            Apply(observedTransition, currentImageX));
        Formula conditions = Grp(
            OpenBracket,
            descentClause, Comma, RowBreak, Grp(),
            lumpabilityClause, Comma, RowBreak, Grp(),
            factorizationClause,
            CloseBracket);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(state, Comma, Sp, readoutType), type), Comma,
            RowBreak, Grp(),
            Typed(readout, Arrow(state, readoutType)), Comma, Sp,
            Typed(transition, Arrow(state, stateLaw)), Comma,
            RowBreak, Grp(),
            Call("ListTFAE", conditions), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
