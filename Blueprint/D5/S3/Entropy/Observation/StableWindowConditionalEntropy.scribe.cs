using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Observation;

internal sealed class StableWindowConditionalEntropyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Entropy/Observation/StableWindowConditionalEntropy."
            + "stable_window_conditional_entropy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stable finite observation kernels have zero next-readout conditional entropy, "
            + "and a full-support law detects kernel stability.",
        H("Stable Window Conditional Entropy"),
        Blocks(Describe.Lean(
            DescribeId.Create("stable-window-conditional-entropy"),
            DeclarationHandle.Create(Declaration),
            H("Kernel stability and zero conditional entropy"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The finite word and its consecutive kernels are the canonical "
                        + "futureReadoutWord objects. The joint law is the deterministic "
                        + "pushforward pairing the word through depth n with the next readout.")),
                Paragraph(Text(
                    "If the consecutive kernels agree, the next readout is constant on every "
                        + "word fiber. The imported point-mass criterion therefore makes its "
                        + "conditional entropy zero for every normalized initial law, including "
                        + "laws that do not have full support.")),
                Paragraph(Text(
                    "Conversely, strict positivity gives every state and every realized word "
                        + "positive mass. Zero conditional entropy then forces both next readouts "
                        + "in any common word fiber to equal the same point-mass value, which "
                        + "reconstructs equality of the consecutive kernels."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("Y");
        Formula outputType = F.Id("O");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula depth = F.Id("n");
        Formula mass = F.Id("p");
        Formula finiteType = Seq(Operatorname, Grp(F.Id("FiniteType")));
        Formula real = F.Id("R");
        Formula natural = F.Id("N");
        Formula word = Call("futureReadoutWord", update, readout, depth);
        Formula nextDepth = Seq(depth, Sp, Plus, Sp, D(1));
        Formula nextWord = Call("futureReadoutWord", update, readout, nextDepth);
        Formula kernelStable = Seq(
            Call("kernel", word), Sp, Eq, Sp, Call("kernel", nextWord));
        Formula probabilityLaw = Call("ProbabilityLaw", mass);
        Formula fullSupport = Call("FullSupport", mass);
        Formula joint = Call(
            "nextReadoutJointLaw", update, readout, mass, depth);
        Formula entropyZero = Seq(
            Call("conditionalEntropy", joint), Sp, Eq, Sp, D(0));
        Formula massQuantifier = Seq(
            Forall, Sp, mass, Colon, Sp, stateType, Sp, To, Sp, real, Comma, Sp);
        Formula forward = Seq(
            Open, kernelStable, Close, Sp, Rightarrow, Sp,
            massQuantifier, Open, probabilityLaw, Close, Sp, Rightarrow, Sp,
            Open, entropyZero, Close);
        Formula reverse = Seq(
            massQuantifier,
            Open, probabilityLaw, Sp, Land, Sp, fullSupport, Close,
            Sp, Rightarrow, Sp, Open, entropyZero, Close,
            Sp, Rightarrow, Sp, Open, kernelStable, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, outputType, Colon, Sp, finiteType, Comma,
            RowBreak, Grp(),
            update, Colon, Sp, stateType, Sp, To, Sp, stateType, Comma, Sp,
            readout, Colon, Sp, stateType, Sp, To, Sp, outputType, Comma, Sp,
            depth, Colon, Sp, natural, Comma,
            RowBreak, Grp(),
            Open, forward, Close, Sp, Land,
            RowBreak, Grp(),
            Open, reverse, Close, Dot,
            End, Grp(F.Id("gathered"))));
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

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
}
