using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Prediction;

internal sealed class PredictiveMemoryEntropyLowerBoundDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Prediction/PredictiveMemoryEntropyLowerBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite exact predictive memory contains at least the conditional information "
            + "carried by the minimal predictive quotient.",
        H("Predictive Memory Entropy Lower Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("predictive-memory-entropy-lower-bound"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "predictive_memory_entropy_lower_bound"),
                H("Exact predictive memories dominate the minimal quotient"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An exact memory factors both the current readout and its updated "
                            + "memory through the memory state. The coarseness clause of the "
                            + "minimal predictive completion theorem therefore makes the "
                            + "canonical predictive projection a deterministic function of "
                            + "the memory.")),
                    Paragraph(Text(
                        "Conditional-entropy data processing gives the inequality for a "
                            + "normalized law. For arbitrary nonnegative finite mass, zero "
                            + "total mass is immediate; otherwise normalize, apply the library "
                            + "theorem, and rescale both conditional entropies.")),
                    Paragraph(Text(
                        "No nonemptiness assumptions are needed. The statement includes empty "
                            + "state carriers, singleton carriers, constant maps, identity "
                            + "maps, and identically zero mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonnegative-mass-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "nonnegative_mass_is_necessary"),
                H("Nonnegative mass is necessary"),
                StatementSource.FromAuthor(CounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take state and memory carrier Bool, constant Unit readout, identity "
                            + "update, identity memory, and signed masses two and minus one. "
                            + "The memory is exact and the predictive quotient is a singleton.")),
                    Paragraph(Text(
                        "The quotient conditional entropy is zero, whereas the identity-memory "
                            + "conditional entropy is minus two times log two. Since log two is "
                            + "positive, the claimed lower-bound inequality fails without "
                            + "nonnegativity."))),
                DescribeRole.Lemma))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula RealNumbers() =>
        Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula FintypeInstance(Formula type) =>
        Seq(
            OpenBracket,
            Operatorname,
            Grp(F.Id("Fintype")),
            Open,
            type,
            Close,
            CloseBracket);

    private static Formula ExactMemory(
        Formula readout,
        Formula update,
        Formula memory) =>
        Call("IsExactPredictiveMemory", readout, update, memory);

    private static Formula JointLaw(
        Formula mass,
        Formula readout,
        Formula state) =>
        Call("predictiveMemoryJointLaw", mass, readout, state);

    private static Formula ConditionalEntropy(Formula law) =>
        Call("conditionalEntropy", law);

    private static Formula PredictiveProjection(Formula update, Formula readout) =>
        Call("predictiveProjection", update, readout);

    private static Formula MainFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula memory = F.Id("M");
        Formula mass = F.Id("mu");
        Formula readout = F.Id("q");
        Formula update = F.Id("F");
        Formula encoder = F.Id("r");
        Formula point = F.Id("x");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Comma, Sp, memory,
            Colon, Sp, TypeUniverse(), Comma, RowBreak, Grp(),
            FintypeInstance(state), Sp, FintypeInstance(output), Sp,
            FintypeInstance(memory), Comma, RowBreak,
            mass, Colon, Sp, Arrow(state, RealNumbers()), Comma, Sp,
            readout, Colon, Sp, Arrow(state, output), Comma, RowBreak,
            update, Colon, Sp, Arrow(state, state), Comma, Sp,
            encoder, Colon, Sp, Arrow(state, memory), Comma, RowBreak,
            Open, Forall, Sp, point, Comma, Sp, D(0), Sp, Leq, Sp,
            Call("mu", point), Close, Sp, Land, Sp,
            ExactMemory(readout, update, encoder), Sp, Rightarrow, RowBreak,
            ConditionalEntropy(JointLaw(
                mass,
                readout,
                PredictiveProjection(update, readout))),
            Sp, Leq, Sp,
            ConditionalEntropy(JointLaw(mass, readout, encoder)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula CounterexampleFormula()
    {
        Formula mass = F.Id("mu");
        Formula readout = F.Id("q");
        Formula identity = F.Id("id");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Call("mu", F.Id("false")), Sp, Eq, Sp, D(2), Comma, Sp,
            Call("mu", F.Id("true")), Sp, Eq, Sp, Minus, D(1), Comma, RowBreak,
            Forall, Sp, F.Id("b"), Colon, Sp, F.Id("Bool"), Comma, Sp,
            Call("q", F.Id("b")), Sp, Eq, Sp, F.Id("star"), Comma, RowBreak,
            Neg, Open, Forall, Sp, F.Id("b"), Comma, Sp, D(0), Sp, Leq, Sp,
            Call("mu", F.Id("b")), Close, Sp, Land, Sp,
            ExactMemory(readout, identity, identity), Sp, Land, RowBreak,
            Neg, Open,
            ConditionalEntropy(JointLaw(
                mass,
                readout,
                PredictiveProjection(identity, readout))),
            Sp, Leq, Sp,
            ConditionalEntropy(JointLaw(mass, readout, identity)), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
