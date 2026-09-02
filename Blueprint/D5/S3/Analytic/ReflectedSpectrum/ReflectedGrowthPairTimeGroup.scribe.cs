using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ReflectedSpectrum;

internal sealed class ReflectedGrowthPairTimeGroupDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairTimeGroup.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The oriented reflected pair is a faithful multiplicative flow, while symmetric observation identifies opposite parameter directions.",
        H("Reflected Growth Pair Time Group"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("oriented-even-odd-observation"),
                DeclarationHandle.Create(Prefix + "orientedEvenOddObservation"),
                H("Joint even-odd observation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The joint observer records both the reflection-invariant even channel and the oriented odd channel already defined by the frozen even-odd decomposition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reflected-time-group"),
                DeclarationHandle.Create(Prefix + "reflected_growth_pair_time_group"),
                H("The reflected pair is a one-parameter multiplicative group"),
                StatementSource.FromAuthor(TimeGroupFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The value at zero is the multiplicative identity, parameter addition becomes coordinatewise multiplication, and parameter reversal gives the inverse pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("oriented-pair-injective"),
                DeclarationHandle.Create(Prefix + "reflected_growth_pair_injective"),
                H("A nonzero split makes the oriented pair faithful"),
                StatementSource.FromAuthor(OrientedPairInjectiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Real exponential injectivity and the nonzero split recover the parameter from the first branch of the full pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetric-observer-loss"),
                DeclarationHandle.Create(Prefix + "reflected_growth_sum_not_injective"),
                H("Symmetric observation loses parameter orientation"),
                StatementSource.FromAuthor(SymmetricObserverLossFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen evenness theorem supplies the explicit collision between parameter values one and minus one, so the branch-forgetting readout is never injective."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-observer-recovery"),
                DeclarationHandle.Create(Prefix + "oriented_even_odd_observation_injective"),
                H("Even and odd channels together restore orientation"),
                StatementSource.FromAuthor(JointObserverRecoveryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Exact branch reconstruction converts equality of joint observations into equality of the positive-rate exponential branch, which recovers the parameter for a nonzero split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("time-recovery-package"),
                DeclarationHandle.Create(Prefix +
                    "oriented_time_recovery_symmetric_time_loss"),
                H("Oriented time recovery and symmetric time loss"),
                StatementSource.FromAuthor(TimeRecoveryPackageFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The packaged theorem separates three facts: the full pair is faithful, the symmetric quotient loses orientation, and adjoining the odd channel restores faithful observation. Negative parameter is represented by the inverse group element."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairEvenOddDecomposition")),
        ]));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Typed(Formula value) => Seq(value, Colon, Sp, Reals());

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

    private static Formula ReflectedPair(Formula delta, Formula time) =>
        Call("reflectedGrowthPair", delta, time);

    private static Formula Injective(Formula function) => Call("Injective", function);

    private static Formula Inverse(Formula value) =>
        Seq(value, Caret, Grp(Seq(Minus, D(1))));

    private static Formula TimeGroupFormula()
    {
        Formula delta = F.Id("delta");
        Formula first = Seq(F.Id("t"), Underscore, D(1));
        Formula second = Seq(F.Id("t"), Underscore, D(2));
        Formula time = F.Id("t");
        Formula identity = Seq(Open, D(1), Comma, Sp, D(1), Close);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(delta), Comma),
            Seq(
                ReflectedPair(delta, D(0)), Sp, Eq, Sp, identity, Sp, Land),
            Seq(
                Grp(Seq(
                    Forall, Sp, Typed(first), Comma, Sp, Typed(second), Comma, Sp,
                    ReflectedPair(delta, Seq(first, Sp, Plus, Sp, second)), Sp, Eq, Sp,
                    ReflectedPair(delta, first), Sp, Cdot, Sp,
                    ReflectedPair(delta, second))),
                Sp, Land),
            Grp(Seq(
                Forall, Sp, Typed(time), Comma, Sp,
                ReflectedPair(delta, Seq(Minus, time)), Sp, Eq, Sp,
                Inverse(ReflectedPair(delta, time)), Dot)),
        ]));
    }

    private static Formula OrientedPairInjectiveFormula()
    {
        Formula delta = F.Id("delta");
        return Disp(Seq(
            Forall, Sp, Typed(delta), Comma, Sp,
            delta, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            Injective(Call("reflectedGrowthPair", delta)), Dot));
    }

    private static Formula SymmetricObserverLossFormula()
    {
        Formula delta = F.Id("delta");
        return Disp(Seq(
            Forall, Sp, Typed(delta), Comma, Sp,
            Neg, Sp, Injective(Call("reflectedGrowthSum", delta)), Dot));
    }

    private static Formula JointObserverRecoveryFormula()
    {
        Formula delta = F.Id("delta");
        return Disp(Seq(
            Forall, Sp, Typed(delta), Comma, Sp,
            delta, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            Injective(Call("orientedEvenOddObservation", delta)), Dot));
    }

    private static Formula TimeRecoveryPackageFormula()
    {
        Formula delta = F.Id("delta");
        Formula time = F.Id("t");

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(delta), Comma, Sp,
                delta, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp, Open),
            Seq(
                Injective(Call("reflectedGrowthPair", delta)), Sp, Land),
            Seq(
                Neg, Sp, Injective(Call("reflectedGrowthSum", delta)), Sp, Land),
            Seq(
                Injective(Call("orientedEvenOddObservation", delta)), Sp, Land),
            Seq(
                Forall, Sp, Typed(time), Comma, Sp,
                ReflectedPair(delta, Seq(Minus, time)), Sp, Eq, Sp,
                Inverse(ReflectedPair(delta, time)), Close, Dot),
        ]));
    }
}
