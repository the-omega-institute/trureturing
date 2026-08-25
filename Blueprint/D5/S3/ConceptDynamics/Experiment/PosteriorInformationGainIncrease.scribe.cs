using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class PosteriorInformationGainIncreaseDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Experiment/PosteriorInformationGainIncrease."
            + "actual_posterior_information_gain_can_increase";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A realized posterior can increase the information value of a deterministic experiment.",
        H("Actual-Posterior Information Gain Can Increase"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-posterior-information-gain-can-increase"),
            DeclarationHandle.Create(Declaration),
            H("Deterministic experiments need not have adaptive diminishing returns"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The hidden carrier has exactly three states. One state has prior mass one "
                        + "half and the other two have mass one quarter each. The first "
                        + "deterministic readout isolates the high-mass state, while the second "
                        + "isolates one of the remaining states.")),
                Paragraph(Text(
                    "The displayed posterior is the Bayes restriction to the positive-probability "
                        + "branch on which the first readout excludes the high-mass state. Both "
                        + "the prior and posterior are displayed as normalized nonnegative laws.")),
                Paragraph(Text(
                    "At each hidden state the joint deterministic output law factors into its two "
                        + "marginals. Nevertheless, the mutual information supplied by the second "
                        + "readout is strictly larger after the realized first-readout branch."))),
            DescribeRole.Theorem))));

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

    private static Formula TheoremFormula()
    {
        Formula zero = D(0);
        Formula one = D(1);
        Formula two = D(2);
        Formula four = D(4);
        Formula stateType = F.Id("X");
        Formula state = F.Id("x");
        Formula boolean = F.Id("Bool");
        Formula value = F.Id("b");
        Formula firstValue = F.Id("a");
        Formula secondValue = F.Id("b");
        Formula mass = F.Mu;
        Formula posterior = F.Id("muPost");
        Formula first = F.Id("A");
        Formula second = F.Id("B");
        Formula conditionalLaw = F.Id("P");
        Formula falseValue = F.Id("false");
        Formula trueValue = F.Id("true");
        Formula none = F.Id("none");
        Formula someValue = Apply(F.Id("some"), value);
        Formula half = new Formula.Fraction(one, two);
        Formula quarter = new Formula.Fraction(one, four);
        Formula eventMass = Apply(Call("pushforward", first, mass), falseValue);
        Formula priorJoint = Call("readoutTargetLaw", mass, second, F.Id("id"));
        Formula posteriorJoint = Call("readoutTargetLaw", posterior, second, F.Id("id"));

        Formula model = Seq(
            stateType, Sp, Eq, Sp, Call("Option", boolean), Comma, RowBreak, Grp(),
            Apply(mass, none), Sp, Eq, Sp, half, Comma, Sp,
            Forall, Sp, value, Colon, Sp, boolean, Comma, Sp,
            Apply(mass, someValue), Sp, Eq, Sp, quarter, Comma, RowBreak, Grp(),
            Apply(first, none), Sp, Eq, Sp, trueValue, Comma, Sp,
            Forall, Sp, value, Colon, Sp, boolean, Comma, Sp,
            Apply(first, someValue), Sp, Eq, Sp, falseValue, Comma, RowBreak, Grp(),
            Apply(second, Apply(F.Id("some"), trueValue)), Sp, Eq, Sp, trueValue,
            Comma, Sp, Apply(second, none), Sp, Eq, Sp, falseValue,
            Comma, Sp, Apply(second, Apply(F.Id("some"), falseValue)), Sp, Eq, Sp,
            falseValue, Comma, RowBreak, Grp(),
            Apply(posterior, state), Sp, Eq, Sp,
            Call("if", Seq(Apply(first, state), Sp, Eq, Sp, falseValue),
                new Formula.Fraction(Apply(mass, state), eventMass), zero),
            Comma, RowBreak, Grp(),
            Apply(conditionalLaw, state, firstValue, secondValue), Sp, Eq, Sp,
            Call("if",
                Seq(Open, firstValue, Comma, Sp, secondValue, Close, Sp, Eq, Sp,
                    Open, Apply(first, state), Comma, Sp, Apply(second, state), Close),
                one, zero));

        Formula priorLaw = Grp(
            Grp(Forall, Sp, state, Colon, Sp, stateType, Comma, Sp,
                zero, Sp, Le, Sp, Apply(mass, state)), Sp, Land, Sp,
            Sum, Underscore, Grp(state), Sp, Apply(mass, state), Sp, Eq, Sp, one);
        Formula posteriorLaw = Grp(
            Grp(Forall, Sp, state, Colon, Sp, stateType, Comma, Sp,
                zero, Sp, Le, Sp, Apply(posterior, state)), Sp, Land, Sp,
            Sum, Underscore, Grp(state), Sp, Apply(posterior, state), Sp, Eq, Sp, one);
        Formula factorization = Grp(
            Forall, Sp, state, Colon, Sp, stateType, Comma, Sp,
            firstValue, Comma, Sp, secondValue, Colon, Sp, boolean, Comma, Sp,
            Apply(conditionalLaw, state, firstValue, secondValue), Sp, Eq, Sp,
            Grp(Sum, Underscore, Grp(F.Id("bPrime")), Sp,
                Apply(conditionalLaw, state, firstValue, F.Id("bPrime"))),
            Sp, Times, Sp,
            Grp(Sum, Underscore, Grp(F.Id("aPrime")), Sp,
                Apply(conditionalLaw, state, F.Id("aPrime"), secondValue)));

        Formula conclusion = Seq(
            priorLaw, Sp, Land, RowBreak, Grp(),
            zero, Sp, Lt, Sp, eventMass, Sp, Land, RowBreak, Grp(),
            posteriorLaw, Sp, Land, RowBreak, Grp(),
            factorization, Sp, Land, RowBreak, Grp(),
            Call("mutualInformation", priorJoint), Sp, Lt, Sp,
            Call("mutualInformation", posteriorJoint));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            model, Colon, RowBreak, Grp(),
            conclusion, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
