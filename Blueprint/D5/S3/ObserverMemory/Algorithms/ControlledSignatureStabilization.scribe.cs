using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class ControlledSignatureStabilizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recursive controlled signatures stabilize at the complete behavior quotient.",
        H("Controlled Signature Stabilization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("controlled-signature-algorithm-correctness"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Algorithms/ControlledSignatureStabilization."
                        + "controlled_signature_algorithm_correctness"),
                H("Controlled signatures compute the complete behavior quotient"),
                StatementSource.FromAuthor(CorrectnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finite nonempty state, input, and readout carriers, let q be a "
                            + "surjective current readout. The depth-zero label is q itself. "
                            + "Each next label consists of q together with the preceding label "
                            + "of every input successor, so the algorithm is constructed directly "
                            + "from the controlled transitions and readout.")),
                    Paragraph(Text(
                        "At every depth m, equality of recursive labels is equivalent to equal "
                            + "readout after every input word of length at most m. Finiteness of "
                            + "the state carrier supplies a common bound for distinguishing "
                            + "words, and the least complete depth is selected from that bound.")),
                    Paragraph(Text(
                        "At this least depth, label equality is complete controlled-behavior "
                            + "equality and remains unchanged at every later round. Quotient "
                            + "congruence then gives a canonical equivalence from the stabilized "
                            + "label quotient to the complete controlled behavior quotient, "
                            + "commuting with the two canonical projections.")),
                    Paragraph(Text(
                        "Repository search found the exact controlled-word semantics in "
                            + "ControlledBehaviorUniversality and a related one-update finite "
                            + "separation argument in FiniteFutureCongruence, but no controlled "
                            + "signature stabilization theorem. Pinned Mathlib supplied "
                            + "Function.ne_iff, Finset.le_sup, Nat.find_spec, Nat.find_min', and "
                            + "Quotient.congrRight, all applied in the proof."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula CorrectnessFormula()
    {
        Formula states = F.Id("Y");
        Formula inputs = F.Id("U");
        Formula outputs = F.Id("O");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula readoutSurjective = F.Id("hreadout");
        Formula depth = F.Id("depth");
        Formula leastDepth = Call("stabilizationDepth", update, readout);
        Formula offset = F.Id("offset");
        Formula firstState = F.Id("y");
        Formula secondState = Seq(F.Id("y"), Apos);
        Formula equivalence = F.Id("outputEquiv");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));

        Formula signatureAtDepthFirst =
            Call("controlledSignature", update, readout, depth, firstState);
        Formula signatureAtDepthSecond =
            Call("controlledSignature", update, readout, depth, secondState);
        Formula boundedAgreement =
            Call("boundedWordEquivalent", update, readout, depth, firstState, secondState);
        Formula completeAtLeast = Seq(
            Forall, Sp, firstState, Comma, Sp, secondState, Colon, Sp, states, Comma, Sp,
            Call("controlledSignature", update, readout, leastDepth, firstState),
            Sp, Eq, Sp,
            Call("controlledSignature", update, readout, leastDepth, secondState),
            Sp, Iff, Sp,
            Call("controlledBehavior", update, readout, firstState), Sp, Eq, Sp,
            Call("controlledBehavior", update, readout, secondState));
        Formula stableAfterLeast = Seq(
            Forall, Sp, offset, Colon, Sp, naturals, Comma, Sp,
            Forall, Sp, firstState, Comma, Sp, secondState, Colon, Sp, states, Comma, Sp,
            Call(
                "controlledSignature", update, readout,
                Seq(leastDepth, Plus, offset), firstState),
            Sp, Eq, Sp,
            Call(
                "controlledSignature", update, readout,
                Seq(leastDepth, Plus, offset), secondState),
            Sp, Iff, Sp,
            Call("controlledSignature", update, readout, leastDepth, firstState),
            Sp, Eq, Sp,
            Call("controlledSignature", update, readout, leastDepth, secondState));
        Formula least = Seq(
            Forall, Sp, depth, Colon, Sp, naturals, Comma, Sp,
            Call("SignatureCompleteAt", update, readout, depth),
            Sp, Rightarrow, Sp, leastDepth, Sp, Leq, Sp, depth);
        Formula quotient = Call("SignatureCompletion", update, readout, leastDepth);
        Formula completion = Call("ControlledCompletion", update, readout);
        Formula projectionLaw = Seq(
            Forall, Sp, firstState, Colon, Sp, states, Comma, Sp,
            Apply(
                equivalence,
                Call("signatureProjection", update, readout, leastDepth, firstState)),
            Sp, Eq, Sp,
            Call("completionProjection", update, readout, firstState));
        Formula output = Seq(
            Exists, Sp, equivalence, Colon, Sp, quotient, Sp, Equiv, Sp, completion,
            Comma, Sp, projectionLaw);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, states, Comma, Sp, inputs, Comma, Sp, outputs,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            OpenBracket, Call("Fintype", states), CloseBracket, Comma, Sp,
            OpenBracket, Call("Finite", inputs), CloseBracket, Comma, Sp,
            OpenBracket, Call("Finite", outputs), CloseBracket, Comma, RowBreak, Grp(),
            OpenBracket, Call("Nonempty", states), CloseBracket, Comma, Sp,
            OpenBracket, Call("Nonempty", inputs), CloseBracket, Comma, Sp,
            OpenBracket, Call("Nonempty", outputs), CloseBracket, Comma, RowBreak, Grp(),
            update, Colon, Sp, inputs, Sp, To, Sp, states, Sp, To, Sp, states,
            Comma, Sp, readout, Colon, Sp, states, Sp, To, Sp, outputs,
            Comma, RowBreak, Grp(),
            readoutSurjective, Colon, Sp, Call("Surjective", readout), Comma, RowBreak,
            Grp(), Open, Forall, Sp, depth, Colon, Sp, naturals, Comma, Sp,
            Forall, Sp, firstState, Comma, Sp, secondState, Colon, Sp, states, Comma, Sp,
            signatureAtDepthFirst, Sp, Eq, Sp, signatureAtDepthSecond,
            Sp, Iff, Sp, boundedAgreement, Close, Sp, Land, RowBreak,
            Grp(), Open, completeAtLeast, Close, Sp, Land, RowBreak,
            Grp(), Open, stableAfterLeast, Close, Sp, Land, RowBreak,
            Grp(), Open, least, Close, Sp, Land, RowBreak,
            Grp(), Open, output, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
