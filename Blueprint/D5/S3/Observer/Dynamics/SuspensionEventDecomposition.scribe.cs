using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Dynamics;

internal sealed class SuspensionEventDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula carrier = F.Id("K");
        Formula transformation = F.Id("T");
        Formula roof = F.Id("r");
        Formula point = F.Id("k");
        Formula phaseCoordinate = F.Id("u");
        Formula time = F.Id("t");
        Formula normal = F.Id("normal");
        Formula count = Call("fst", normal);
        Formula residualCoordinate = Call("snd", normal);
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula roofCoordinate = F.Id("RoofCoordinate");
        Formula sum = Call("birkhoffSum", transformation, roof, count, point);
        Formula nextSum = Call(
            "birkhoffSum", transformation, roof,
            Seq(count, Sp, Plus, Sp, D(1)), point);
        Formula initialHeight = Call("physicalHeight", roof, point, phaseCoordinate);
        Formula finalPoint = Call("iterate", transformation, count, point);
        Formula finalHeight = Call(
            "physicalHeight", roof, finalPoint, residualCoordinate);
        Formula elapsed = Seq(initialHeight, Sp, Plus, Sp, time);
        Formula initialClass = Call(
            "canonicalSuspensionClass", transformation, roof, point, phaseCoordinate);
        Formula finalClass = Call(
            "canonicalSuspensionClass",
            transformation,
            roof,
            finalPoint,
            residualCoordinate);
        Formula flowAtInitial = Call(
            "suspensionFlow", transformation, roof, time, initialClass);
        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, carrier, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma,
            RowBreak, Grp(),
            OpenBracket, Call("TopologicalSpace", carrier), CloseBracket, Comma, Sp,
            OpenBracket, Call("CompactSpace", carrier), CloseBracket, Comma,
            RowBreak, Grp(),
            transformation, Colon, Sp, Call("Homeomorph", carrier, carrier), Comma, Sp,
            roof, Colon, Sp, carrier, Sp, To, Sp, reals, Comma,
            RowBreak, Grp(),
            Call("Continuous", roof), Sp, Land, Sp,
            Open, Forall, Sp, F.Id("x"), Colon, Sp, carrier, Comma, Sp,
            D(0), Sp, Lt, Sp, Call("r", F.Id("x")), Close, Comma,
            RowBreak, Grp(),
            point, Colon, Sp, carrier, Comma, Sp,
            phaseCoordinate, Colon, Sp, roofCoordinate, Comma, Sp,
            time, Colon, Sp, reals, Comma, Sp,
            D(0), Sp, Leq, Sp, time,
            RowBreak, Grp(), Rightarrow, Sp,
            Exists, Bang, Sp, normal, Colon, Sp,
            naturals, Sp, Times, Sp, roofCoordinate, Comma,
            RowBreak, Grp(),
            sum, Sp, Leq, Sp, elapsed, Sp, Land,
            RowBreak, Grp(),
            elapsed, Sp, Lt, Sp, nextSum, Sp, Land,
            RowBreak, Grp(),
            finalHeight, Sp, Eq, Sp, elapsed, Sp, Minus, Sp, sum, Sp, Land,
            RowBreak, Grp(),
            flowAtInitial, Sp, Eq, Sp, finalClass, Sp, Land,
            RowBreak, Grp(),
            elapsed, Sp, Eq, Sp, sum, Sp, Plus, Sp, finalHeight, Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A positive-roof suspension flow splits uniquely into event count and residual phase.",
            H("Suspension Event Decomposition"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("continuous-time-discrete-event-decomposition"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/Dynamics/SuspensionEventDecomposition."
                            + "continuous_time_discrete_event_decomposition"),
                    H("Continuous time has a unique event-phase decomposition"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The frozen suspension carrier uses a normalized leaf coordinate. "
                                + "Multiplication by the positive roof gives its nonnegative "
                                + "physical phase, so no separate sign hypothesis is needed.")),
                        Paragraph(Text(
                            "Literal forward translation is first performed on a private "
                                + "nonnegative-height cover. Normalization respects every roof "
                                + "crossing and transports the translated class back to the "
                                + "canonical suspension quotient.")),
                        Paragraph(Text(
                            "Compactness and roof positivity force the Birkhoff sums past the "
                                + "translated physical phase. The least crossing index supplies "
                                + "both half-open bounds; division by the final positive roof "
                                + "produces the residual leaf coordinate.")),
                        Paragraph(Text(
                            "The bounds determine the event count uniquely, while positivity "
                                + "makes physical height injective within the final leaf. Thus "
                                + "the discrete count and residual coordinate are jointly unique "
                                + "and recover the complete translated time coordinate."))),
                    DescribeRole.Theorem))));
    }
}
