using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class PointwiseAlmostEverywhereSeparationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pointwise fiber knowledge implies a.e. knowledge, but not conversely.",
        H("Pointwise and Probability Knowledge Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pointwise-sufficient-definition"),
                Handle("PointwiseSufficient"),
                H("Pointwise sufficiency"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A target is pointwise sufficient when it is constant on every "
                        + "fiber of the readout, with no exceptional state."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("almost-everywhere-sufficient-definition"),
                Handle("AlmostEverywhereSufficient"),
                H("Almost-everywhere sufficiency"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A target is almost-everywhere sufficient when some factor through "
                        + "the readout agrees with it outside a null set."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pointwise-implies-almost-everywhere"),
                Handle("pointwise_sufficient_implies_almost_everywhere_sufficient"),
                H("Pointwise sufficiency implies almost-everywhere sufficiency"),
                StatementSource.FromAuthor(PointwiseImpliesAe()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The repository's answerability criterion constructs the exact "
                        + "factor under an anchor. The pinned general criterion weakens "
                        + "that premise to target nonemptiness, after which exact equality "
                        + "implies almost-everywhere equality under every measure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonempty-target-is-necessary"),
                Handle("nonempty_target_is_necessary"),
                H("Target nonemptiness cannot be deleted in full generality"),
                StatementSource.FromAuthor(TargetNonemptyNecessary()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an empty state and target type but a one-point readout type, "
                        + "fiber constancy is vacuous while no factor from PUnit to Empty "
                        + "can exist."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-measure-ae-sufficiency"),
                Handle("zero_measure_almost_everywhere_sufficient"),
                H("A supplied factor is sufficient under the zero measure"),
                StatementSource.FromAuthor(ZeroMeasure()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "All equalities hold almost everywhere for the zero measure. The "
                        + "factor is supplied explicitly so no hidden inhabitance premise "
                        + "is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("injective-readout-pointwise-sufficiency"),
                Handle("injective_readout_pointwise_sufficient"),
                H("Injective readouts are pointwise sufficient"),
                StatementSource.FromAuthor(InjectiveReadout()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equality of injective readout values forces equality of states, so "
                        + "every target is constant on each singleton fiber. Identity "
                        + "readouts are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("constant-target-sufficiency"),
                Handle("constant_target_sufficient"),
                H("Constant targets satisfy both notions"),
                StatementSource.FromAuthor(ConstantTarget()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A constant target has no fiber defect and factors through every "
                        + "readout by the same constant, including constant and zero maps."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("null-point-measure-definition"),
                Handle("nullPointMeasure"),
                H("The counterexample measure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The counterexample uses Lebesgue measure on R."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("null-point-readout-definition"),
                Handle("nullPointReadout"),
                H("The counterexample readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The readout is constant from R to PUnit, so the whole state space "
                        + "is one fiber."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("null-point-target-definition"),
                Handle("nullPointTarget"),
                H("The counterexample target"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Boolean target is true only at zero and false everywhere else."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("null-point-factor-definition"),
                Handle("nullPointFactor"),
                H("The counterexample factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The factor on PUnit is constantly false and differs from the target "
                        + "only at the origin."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("null-point-measure-is-nonzero"),
                Handle("null_point_measure_ne_zero"),
                H("The counterexample measure is nonzero"),
                StatementSource.FromAuthor(MeasureNonzero()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Lebesgue measure assigns infinite mass to the real line, excluding "
                        + "the vacuous zero-measure construction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("null-point-singleton-is-null"),
                Handle("null_point_singleton_measure_zero"),
                H("The exceptional singleton is null"),
                StatementSource.FromAuthor(SingletonNull()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mathlib's Lebesgue singleton theorem explicitly verifies that the "
                        + "origin has measure zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-fiber-different-target"),
                Handle("null_point_same_fiber_different_target"),
                H("One fiber contains two different target values"),
                StatementSource.FromAuthor(FiberDefect()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The points zero and one have the same PUnit readout, while the "
                        + "target is respectively true and false."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("null-point-ae-sufficiency"),
                Handle("null_point_almost_everywhere_sufficient"),
                H("The null-point target factors almost everywhere"),
                StatementSource.FromAuthor(NullPointAe()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Outside zero, the target equals the constantly false factor. The "
                        + "singleton calculation makes that exceptional set null."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fpod-principle-118-1"),
                Handle("fpod_principle_118_1"),
                H("Almost-everywhere sufficiency is not pointwise sufficiency"),
                StatementSource.FromAuthor(Principle()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The explicit target factors through the constant readout almost "
                            + "everywhere but is not constant on that readout's sole fiber.")),
                    Paragraph(Text(
                        "Strong lumpability instead characterizes pointwise descent of "
                            + "pushed-forward PMF rows. The conull-image theorem instead "
                            + "pulls measures back along injections; neither gives this "
                            + "strict comparison."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(
        "D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation."
            + name);

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

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Pointwise(Formula readout, Formula target) =>
        Apply(F.Id("PointwiseSufficient"), readout, target);

    private static Formula Ae(Formula measure, Formula readout, Formula target) =>
        Apply(F.Id("AlmostEverywhereSufficient"), measure, readout, target);

    private static Formula PointwiseImpliesAe()
    {
        Formula xType = F.Id("X");
        Formula qType = F.Id("Q");
        Formula yType = F.Id("Y");
        Formula measure = F.Id("mu");
        Formula readout = F.Id("q");
        Formula target = F.Id("T");
        return Disp(Seq(
            Apply(F.Id("Nonempty"), yType), Comma, Sp,
            measure, Colon, Sp, Apply(F.Id("Measure"), xType), Comma, Sp,
            readout, Colon, Sp, Arrow(xType, qType), Comma, Sp,
            target, Colon, Sp, Arrow(xType, yType), Comma, RowBreak, Grp(),
            Pointwise(readout, target), Sp, Rightarrow, Sp,
            Ae(measure, readout, target), Dot));
    }

    private static Formula TargetNonemptyNecessary()
    {
        Formula readout = F.Id("q");
        Formula target = F.Id("T");
        return Disp(Seq(
            Exists, Sp, readout, Colon, Sp,
            Arrow(F.Id("Empty"), F.Id("PUnit")), Comma, Sp,
            target, Colon, Sp, Arrow(F.Id("Empty"), F.Id("Empty")), Comma, Sp,
            Pointwise(readout, target), Sp, Land, Sp,
            Neg, Sp, Ae(D(0), readout, target), Dot));
    }

    private static Formula ZeroMeasure()
    {
        Formula readout = F.Id("q");
        Formula target = F.Id("T");
        Formula factor = F.Id("Tbar");
        return Disp(Seq(
            Forall, Sp, readout, Comma, Sp, target, Comma, Sp, factor, Comma, Sp,
            Ae(D(0), readout, target), Dot));
    }

    private static Formula InjectiveReadout()
    {
        Formula readout = F.Id("q");
        Formula target = F.Id("T");
        return Disp(Seq(
            Apply(F.Id("Injective"), readout), Sp, Rightarrow, Sp,
            Pointwise(readout, target), Dot));
    }

    private static Formula ConstantTarget()
    {
        Formula readout = F.Id("q");
        Formula constant = Apply(F.Id("const"), F.Id("c"));
        return Disp(Seq(
            Pointwise(readout, constant), Sp, Land, Sp,
            Ae(F.Id("mu"), readout, constant), Dot));
    }

    private static Formula MeasureNonzero() => Disp(Seq(
        F.Id("nullPointMeasure"), Sp, Neq, Sp, D(0), Dot));

    private static Formula SingletonNull() => Disp(Seq(
        Apply(F.Id("nullPointMeasure"),
            Seq(OpenBrace, D(0), CloseBrace)), Sp, Eq, Sp, D(0), Dot));

    private static Formula FiberDefect()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula readout = F.Id("nullPointReadout");
        Formula target = F.Id("nullPointTarget");
        return Disp(Seq(
            Exists, Sp, x, Comma, Sp, y, Colon, Sp, Mathbb, Grp(F.Id("R")),
            Comma, Sp, Apply(readout, x), Sp, Eq, Sp, Apply(readout, y),
            Sp, Land, Sp, Apply(target, x), Sp, Neq, Sp, Apply(target, y), Dot));
    }

    private static Formula NullPointAe() => Disp(Seq(
        Ae(F.Id("nullPointMeasure"), F.Id("nullPointReadout"),
            F.Id("nullPointTarget")), Dot));

    private static Formula Principle()
    {
        Formula readout = F.Id("nullPointReadout");
        Formula target = F.Id("nullPointTarget");
        return Disp(Seq(
            Ae(F.Id("nullPointMeasure"), readout, target), Sp, Land, Sp,
            Neg, Sp, Pointwise(readout, target), Dot));
    }
}
