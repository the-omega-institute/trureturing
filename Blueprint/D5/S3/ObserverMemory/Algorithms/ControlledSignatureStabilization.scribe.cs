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
        Formula depth = F.Id("m");
        Formula leastDepth = Seq(F.Id("m"), Underscore, Grp(Star));
        Formula offset = F.Id("r");
        Formula firstState = F.Id("y");
        Formula secondState = Seq(F.Id("y"), Apos);
        Formula word = F.Id("w");
        Formula behavior = F.Id("B");
        Formula completion = F.Id("Z");
        Formula equivalence = F.Id("e");

        Formula signatureAtDepthFirst = Call("c", depth, firstState);
        Formula signatureAtDepthSecond = Call("c", depth, secondState);
        Formula boundedAgreement = Seq(
            Forall, Sp, word, InMacro, Sp, Call("Words", inputs), Comma, Sp,
            Call("length", word), Sp, Leq, Sp, depth, Sp, Rightarrow, Sp,
            Call("readoutAfter", update, readout, word, firstState), Sp, Eq, Sp,
            Call("readoutAfter", update, readout, word, secondState));
        Formula completeAtLeast = Seq(
            Forall, Sp, firstState, Comma, Sp, secondState, Comma, Sp,
            Call("c", leastDepth, firstState), Sp, Eq, Sp,
            Call("c", leastDepth, secondState), Sp, Iff, Sp,
            Apply(behavior, firstState), Sp, Eq, Sp, Apply(behavior, secondState));
        Formula stableAfterLeast = Seq(
            Forall, Sp, offset, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Forall, Sp, firstState, Comma, Sp, secondState, Comma, Sp,
            Call("c", Seq(leastDepth, Plus, offset), firstState), Sp, Eq, Sp,
            Call("c", Seq(leastDepth, Plus, offset), secondState), Sp, Iff, Sp,
            Call("c", leastDepth, firstState), Sp, Eq, Sp,
            Call("c", leastDepth, secondState));
        Formula least = Seq(
            Forall, Sp, depth, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Call("CompleteAt", depth), Sp, Rightarrow, Sp, leastDepth, Sp, Leq, Sp, depth);
        Formula quotient = Call("SignatureQuotient", leastDepth);
        Formula projectionLaw = Seq(
            Forall, Sp, firstState, InMacro, Sp, states, Comma, Sp,
            Apply(equivalence, Call("signatureClass", leastDepth, firstState)), Sp, Eq, Sp,
            Call("behaviorClass", firstState));
        Formula output = Seq(
            Exists, Sp, equivalence, Colon, Sp, quotient, Sp, Equiv, Sp, completion,
            Comma, Sp, projectionLaw);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, states, Comma, Sp, inputs, Comma, Sp, outputs, Comma, RowBreak,
            Call("FiniteNonempty", states), Comma, Sp,
            Call("FiniteNonempty", inputs), Comma, Sp,
            Call("FiniteNonempty", outputs), Comma, RowBreak,
            update, Colon, Sp, inputs, Sp, To, Sp, states, Sp, To, Sp, states,
            Comma, Sp, readout, Colon, Sp, states, Sp, To, Sp, outputs,
            Comma, Sp, Call("Surjective", readout), Comma, RowBreak,
            Open, Forall, Sp, depth, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Forall, Sp, firstState, Comma, Sp, secondState, Comma, Sp,
            signatureAtDepthFirst, Sp, Eq, Sp, signatureAtDepthSecond,
            Sp, Iff, Sp, boundedAgreement, Close, Sp, Land, RowBreak,
            Open, completeAtLeast, Close, Sp, Land, RowBreak,
            Open, stableAfterLeast, Close, Sp, Land, RowBreak,
            Open, least, Close, Sp, Land, RowBreak,
            Open, output, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
