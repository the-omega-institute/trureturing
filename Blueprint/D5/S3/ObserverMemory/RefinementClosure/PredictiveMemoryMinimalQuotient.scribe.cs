using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure;

internal sealed class PredictiveMemoryMinimalQuotientDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ObserverMemory/RefinementClosure/PredictiveMemoryMinimalQuotient."
            + "predictive_memory_minimal_quotient";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every exact predictive memory maps uniquely onto the completed readout-kernel quotient.",
        H("Predictive Memory Minimal Quotient"),
        Blocks(Describe.Lean(
            DescribeId.Create("predictive-memory-minimal-quotient"),
            DeclarationHandle.Create(Declaration),
            H("The predictive quotient is the coarsest exact memory"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The two public premises are exactly the predictive-memory conditions: the "
                        + "current readout factors through r and r carries a descended update.")),
                Paragraph(Text(
                    "The canonical complete itinerary is therefore determined by r. Choosing a "
                        + "representative only inside the realized image of r sends each memory "
                        + "state to its class in the kernel quotient of the complete itinerary.")),
                Paragraph(Text(
                    "Representative independence follows from equality of the factored complete "
                        + "itineraries. Surjectivity of the canonical range factorization then "
                        + "proves uniqueness without requiring r to be onto its ambient carrier."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula state = F.Id("X");
        Formula output = F.Id("B");
        Formula memory = F.Id("M");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula summary = F.Id("r");
        Formula readoutFactor = F.Id("f");
        Formula induced = F.Id("G");
        Formula theta = F.Id("theta");
        Formula completedState = Call("CompletedState", update, readout);
        Formula memoryImage = Call("range", summary);

        Formula readoutFactors = Seq(
            Exists, Sp, Typed(readoutFactor, Arrow(memory, output)), Comma, Sp,
            readout, Sp, Eq, Sp, readoutFactor, Sp, Circ, Sp, summary);
        Formula updateFactors = Seq(
            Exists, Sp, Typed(induced, Arrow(memory, memory)), Comma, Sp,
            summary, Sp, Circ, Sp, update, Sp, Eq, Sp,
            induced, Sp, Circ, Sp, summary);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(state, Comma, Sp, output, Comma, Sp, memory), type),
            Comma, RowBreak, Grp(),
            Typed(update, Arrow(state, state)), Comma, Sp,
            Typed(readout, Arrow(state, output)), Comma, Sp,
            Typed(summary, Arrow(state, memory)), Comma, RowBreak, Grp(),
            Open, readoutFactors, Close, Sp, Land, Sp,
            Open, updateFactors, Close, Sp, Rightarrow, RowBreak, Grp(),
            Exists, Bang, Sp,
            Typed(theta, Arrow(memoryImage, completedState)), Comma, RowBreak, Grp(),
            Call("completionProjection", update, readout), Sp, Eq, Sp,
            theta, Sp, Circ, Sp, Call("rangeFactorization", summary), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
