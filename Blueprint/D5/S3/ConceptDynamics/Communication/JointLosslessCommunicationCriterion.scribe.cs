using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Communication;

internal sealed class JointLosslessCommunicationCriterionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Communication/JointLosslessCommunicationCriterion."
            + "joint_lossless_communication_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint communication is lossless on realized behavior records, while correlated "
            + "coordinates can compensate for a lossy component.",
        H("Joint Lossless Communication Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("joint-lossless-communication-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Losslessness is injectivity on realized joint behavior"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The full behavior is the canonical dependent jointReadout of all "
                        + "coordinate behaviors. Its message applies each coordinate encoder "
                        + "to the corresponding realized component.")),
                Paragraph(Text(
                    "Equality of the message and behavior kernels is equivalent to "
                        + "injectivity of that coordinatewise encoder on the actual joint "
                        + "behavior image. Injectivity outside the realized image is irrelevant.")),
                Paragraph(Text(
                    "Coordinatewise injectivity on every realized marginal image is a "
                        + "sufficient condition. It is not necessary: two correlated Boolean "
                        + "coordinates remain jointly lossless when the false-index encoder is "
                        + "constant and the true-index encoder preserves the shared bit.")),
                Paragraph(Text(
                    "The final public clause imports the canonical least-common-refinement "
                        + "result: a compatible surjective implementation covering both "
                        + "quotients has a unique surjective descent to their intersection "
                        + "quotient."))),
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

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Kernel(Formula map) => Call("ker", map);

    private static Formula JointCompression(Formula compression) =>
        Seq(
            LambdaLower, Sp, F.Id("record"), Comma, Sp, F.Id("i"), Sp, Mapsto, Sp,
            Apply(Apply(compression, F.Id("i")), Apply(F.Id("record"), F.Id("i"))));

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula behaviorFamily = F.Id("B");
        Formula messageFamily = F.Id("C");
        Formula behavior = F.Id("behavior");
        Formula compression = F.Id("compress");
        Formula fullBehavior = Apply(F.Id("jointReadout"), behavior);
        Formula jointCompression = JointCompression(compression);
        Formula jointMessage = Apply(F.Id("messageConcept"), fullBehavior, jointCompression);
        Formula kernelCriterion = Seq(
            Kernel(jointMessage), Sp, Eq, Sp, Kernel(fullBehavior), Sp, Iff, Sp,
            Call("InjOn", jointCompression, Call("range", fullBehavior)));
        Formula coordinateSufficiency = Seq(
            Open, Forall, Sp, F.Id("i"), InMacro, Sp, indexType, Comma, Sp,
            Call("InjOn", Apply(compression, F.Id("i")),
                Call("range", Apply(behavior, F.Id("i")))), Close,
            Sp, Rightarrow, Sp, Kernel(jointMessage), Sp, Eq, Sp, Kernel(fullBehavior));

        Formula counterBehavior = F.Id("behaviorC");
        Formula counterCompression = F.Id("compressC");
        Formula counterFull = Apply(F.Id("jointReadout"), counterBehavior);
        Formula counterJointCompression = JointCompression(counterCompression);
        Formula counterMessage =
            Apply(F.Id("messageConcept"), counterFull, counterJointCompression);
        Formula countermodel = Seq(
            Exists, Sp,
            Typed(counterBehavior,
                Seq(Pi, Sp, F.Id("i"), Colon, Sp, F.Id("Bool"), Comma, Sp,
                    Arrow(F.Id("Bool"), F.Id("Bool")))), Comma, Sp,
            Typed(counterCompression,
                Seq(Pi, Sp, F.Id("i"), Colon, Sp, F.Id("Bool"), Comma, Sp,
                    Arrow(F.Id("Bool"), F.Id("Bool")))), Comma, RowBreak, Grp(),
            Kernel(counterMessage), Sp, Eq, Sp, Kernel(counterFull), Sp, Land, Sp,
            Neg, Open, Forall, Sp, F.Id("i"), InMacro, Sp, F.Id("Bool"), Comma, Sp,
            Call("InjOn", Apply(counterCompression, F.Id("i")),
                Call("range", Apply(counterBehavior, F.Id("i")))), Close);

        Formula yType = F.Id("Y");
        Formula wType = F.Id("W");
        Formula first = F.Id("R1");
        Formula second = F.Id("R2");
        Formula projection = F.Id("r");
        Formula toFirst = F.Id("p1");
        Formula toSecond = F.Id("p2");
        Formula descend = F.Id("h");
        Formula y = F.Id("y");
        Formula quotientFirst = Call("Quotient", first);
        Formula quotientSecond = Call("Quotient", second);
        Formula intersection = Call("inf", first, second);
        Formula quotientIntersection = Call("Quotient", intersection);
        Formula commonRefinement = Seq(
            Forall, Sp, yType, Comma, Sp, wType, Colon, Sp, F.Id("Type"), Comma, Sp,
            Typed(first, Call("Setoid", yType)), Comma, Sp,
            Typed(second, Call("Setoid", yType)), Comma, RowBreak, Grp(),
            Typed(projection, Arrow(yType, wType)), Comma, Sp,
            Typed(toFirst, Arrow(wType, quotientFirst)), Comma, Sp,
            Typed(toSecond, Arrow(wType, quotientSecond)), Comma, RowBreak, Grp(),
            Call("Surjective", projection), Sp, Land, Sp,
            Call("Surjective", toFirst), Sp, Land, Sp,
            Call("Surjective", toSecond), Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, y, InMacro, Sp, yType, Comma, Sp,
            Apply(toFirst, Apply(projection, y)), Sp, Eq, Sp,
            Call("class", y, first), Close, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, y, InMacro, Sp, yType, Comma, Sp,
            Apply(toSecond, Apply(projection, y)), Sp, Eq, Sp,
            Call("class", y, second), Close, Sp, Rightarrow, RowBreak, Grp(),
            Exists, Bang, Sp, Typed(descend, Arrow(wType, quotientIntersection)), Comma, Sp,
            Call("Surjective", descend), Sp, Land, Sp,
            Forall, Sp, y, InMacro, Sp, yType, Comma, Sp,
            Apply(descend, Apply(projection, y)), Sp, Eq, Sp,
            Call("class", y, intersection));

        Formula behaviorType = Seq(
            Pi, Sp, F.Id("i"), Colon, Sp, indexType, Comma, Sp,
            Arrow(stateType, Apply(behaviorFamily, F.Id("i"))));
        Formula compressionType = Seq(
            Pi, Sp, F.Id("i"), Colon, Sp, indexType, Comma, Sp,
            Arrow(Apply(behaviorFamily, F.Id("i")),
                Apply(messageFamily, F.Id("i"))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, indexType, Comma, Sp, stateType, Colon, Sp, F.Id("Type"), Comma,
            RowBreak, Grp(),
            Typed(behaviorFamily, Arrow(indexType, F.Id("Type"))), Comma, Sp,
            Typed(messageFamily, Arrow(indexType, F.Id("Type"))), Comma, RowBreak, Grp(),
            Typed(behavior, behaviorType), Comma, Sp,
            Typed(compression, compressionType), Comma, RowBreak, Grp(),
            Open, kernelCriterion, Close, Sp, Land, RowBreak, Grp(),
            Open, coordinateSufficiency, Close, Sp, Land, RowBreak, Grp(),
            Open, countermodel, Close, Sp, Land, RowBreak, Grp(),
            Open, commonRefinement, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
