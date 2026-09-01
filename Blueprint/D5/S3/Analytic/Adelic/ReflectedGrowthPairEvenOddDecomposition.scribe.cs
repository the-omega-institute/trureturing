using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class ReflectedGrowthPairEvenOddDecompositionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/Adelic/ReflectedGrowthPairEvenOddDecomposition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Split a reflected growth pair into an invariant even channel and an oriented odd channel.",
        H("Reflected Growth Pair Even-Odd Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("even-observation-definition"),
                DeclarationHandle.Create(Prefix + "evenObservation"),
                H("The reflection-invariant even channel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The even channel averages the two frozen reflected branches. It forgets "
                        + "which branch expands and which contracts while retaining their "
                        + "reflection-invariant magnitude."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("odd-observation-definition"),
                DeclarationHandle.Create(Prefix + "oddObservation"),
                H("The oriented odd channel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The odd channel is half the branch difference. Parameter reversal changes "
                        + "its sign, so it records the orientation erased by the symmetric sum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("even-odd-decomposition"),
                DeclarationHandle.Create(Prefix +
                    "reflected_growth_pair_even_odd_decomposition"),
                H("Even and odd channels reconstruct the reflected pair"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The even channel is invariant under parameter reversal and the odd "
                            + "channel is anti-invariant. Their sum and difference recover the "
                            + "two oriented exponential branches exactly.")),
                    Paragraph(Text(
                        "The frozen reciprocal product becomes the Lorentzian identity E squared "
                            + "minus O squared equals one. This is a finite scalar identity and "
                            + "does not assert a completed-zeta realization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("odd-channel-zero-locus"),
                DeclarationHandle.Create(Prefix + "odd_observation_eq_zero_iff"),
                H("The odd channel vanishes only at zero split or zero parameter"),
                StatementSource.FromAuthor(ZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The oriented channel loses all signal exactly when the reflected split is "
                        + "absent or when the observation is taken at the reflection center."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-odd-orientation"),
                DeclarationHandle.Create(Prefix +
                    "odd_observation_positive_of_forward_orientation"),
                H("Positive split and positive parameter give positive odd orientation"),
                StatementSource.FromAuthor(OrientationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen forward-orientation theorem orders the expanding branch above "
                        + "the contracting branch. Their half-difference is therefore positive."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Adelic/ReflectedGrowthPairSecondOrderSpectrum")),
        ]));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Typed(Formula value) => Seq(value, Colon, Sp, Reals());

    private static Formula PowerTwo(Formula value) => Seq(value, Caret, Grp(D(2)));

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

    private static Formula MainFormula()
    {
        Formula delta = F.Id("delta");
        Formula time = F.Id("t");
        Formula negativeTime = Seq(Minus, time);
        Formula even = Call("evenObservation", delta, time);
        Formula odd = Call("oddObservation", delta, time);
        return Disp(Seq(
            Forall, Sp, Typed(delta), Comma, Sp, Typed(time), Comma, Sp,
            Call("evenObservation", delta, negativeTime), Sp, Eq, Sp, even, Sp, Land, Sp,
            Call("oddObservation", delta, negativeTime), Sp, Eq, Sp, Minus, odd, Sp, Land, Sp,
            even, Sp, Plus, Sp, odd, Sp, Eq, Sp,
            Call("positiveRateBranch", delta, time), Sp, Land, Sp,
            even, Sp, Minus, Sp, odd, Sp, Eq, Sp,
            Call("negativeRateBranch", delta, time), Sp, Land, Sp,
            PowerTwo(even), Sp, Minus, Sp, PowerTwo(odd), Sp, Eq, Sp, D(1), Dot));
    }

    private static Formula ZeroFormula()
    {
        Formula delta = F.Id("delta");
        Formula time = F.Id("t");
        return Disp(Seq(
            Forall, Sp, Typed(delta), Comma, Sp, Typed(time), Comma, Sp,
            Call("oddObservation", delta, time), Sp, Eq, Sp, D(0), Sp, Iff, Sp,
            delta, Sp, Eq, Sp, D(0), Sp, Lor, Sp, time, Sp, Eq, Sp, D(0), Dot));
    }

    private static Formula OrientationFormula()
    {
        Formula delta = F.Id("delta");
        Formula time = F.Id("t");
        return Disp(Seq(
            Forall, Sp, Typed(delta), Comma, Sp, Typed(time), Comma, Sp,
            D(0), Sp, Lt, Sp, delta, Sp, Land, Sp, D(0), Sp, Lt, Sp, time,
            Sp, Rightarrow, Sp, D(0), Sp, Lt, Sp,
            Call("oddObservation", delta, time), Dot));
    }
}
