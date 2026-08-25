using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Information;

internal sealed class EqualEntropyTargetValueContrastDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Information/EqualEntropyTargetValueContrast."
            + "equal_entropy_target_value_contrast";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal information quantity can carry opposite target value.",
        H("Equal Entropy, Different Target Value"),
        Blocks(Describe.Lean(
            DescribeId.Create("equal-entropy-target-value-contrast"),
            DeclarationHandle.Create(Declaration),
            H("Equal entropy and compression do not imply equal target sufficiency"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The state is a uniformly distributed pair of Boolean coordinates. The two "
                        + "concepts report the first and second coordinates, while the target is "
                        + "the first coordinate.")),
                Paragraph(Text(
                    "Both canonical pushforward laws have entropy log two. Both readouts attain "
                        + "two labels out of four source states, so their displayed label counts "
                        + "and output-to-input cardinality ratios agree.")),
                Paragraph(Text(
                    "The conditional target entropy is zero after the first readout and log two "
                        + "after the second. The final two public conjuncts state the same contrast "
                        + "structurally: the target factors through the first readout but not the "
                        + "second."))),
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
        Formula state = F.Id("X");
        Formula point = F.Id("x");
        Formula mass = F.Id("mu");
        Formula first = new Formula.Subscript(F.Id("C"), one);
        Formula second = new Formula.Subscript(F.Id("C"), two);
        Formula target = F.Id("T");
        Formula boolean = F.Id("Bool");
        Formula firstProjection = Call("fst", point);
        Formula secondProjection = Call("snd", point);
        Formula logTwo = Call("log", two);
        Formula firstLaw = Call("conceptLaw", mass, first);
        Formula secondLaw = Call("conceptLaw", mass, second);
        Formula firstLabels = Call("ncard", Call("range", first));
        Formula secondLabels = Call("ncard", Call("range", second));
        Formula sourceLabels = Call("card", state);
        Formula half = new Formula.Fraction(one, two);

        Formula model = Seq(
            state, Sp, Eq, Sp, boolean, Sp, Times, Sp, boolean, Comma, Sp,
            Apply(mass, point), Sp, Eq, Sp, new Formula.Fraction(one, four),
            Comma, RowBreak, Grp(),
            Apply(first, point), Sp, Eq, Sp, firstProjection, Comma, Sp,
            Apply(second, point), Sp, Eq, Sp, secondProjection, Comma, Sp,
            Apply(target, point), Sp, Eq, Sp, firstProjection);

        Formula conclusion = Seq(
            Call("shannonEntropy", firstLaw), Sp, Eq, Sp, logTwo,
            Sp, Land, RowBreak, Grp(),
            Call("shannonEntropy", secondLaw), Sp, Eq, Sp, logTwo,
            Sp, Land, RowBreak, Grp(),
            firstLabels, Sp, Eq, Sp, two, Sp, Land, Sp,
            secondLabels, Sp, Eq, Sp, two,
            Sp, Land, RowBreak, Grp(),
            new Formula.Fraction(firstLabels, sourceLabels), Sp, Eq, Sp, half,
            Sp, Land, Sp,
            new Formula.Fraction(secondLabels, sourceLabels), Sp, Eq, Sp, half,
            Sp, Land, RowBreak, Grp(),
            Call("targetResidualEntropy", mass, first, target), Sp, Eq, Sp, zero,
            Sp, Land, RowBreak, Grp(),
            Call("targetResidualEntropy", mass, second, target), Sp, Eq, Sp, logTwo,
            Sp, Land, RowBreak, Grp(),
            Call("Refines", target, first), Sp, Land, Sp,
            Neg, Sp, Call("Refines", target, second));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            model, Colon, RowBreak, Grp(),
            conclusion, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
