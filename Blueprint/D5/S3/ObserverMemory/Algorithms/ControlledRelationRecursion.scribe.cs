using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class ControlledRelationRecursionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded controlled behavior relations satisfy the current-readout recursion.",
        H("Controlled Relation Recursion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("controlled-behavior-relation-recursion"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Algorithms/ControlledRelationRecursion."
                        + "controlled_behavior_relation_recursion"),
                H("Controlled behavior relations obey the one-step recursion"),
                StatementSource.FromAuthor(RecursionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary state, input, and readout carriers, construct the depth-m "
                            + "relation by requiring equal readouts after every input word of "
                            + "length at most m. The current-readout kernel is separately "
                            + "constructed from equality under the readout map.")),
                    Paragraph(Text(
                        "At depth zero only the empty input word is tested, giving the readout "
                            + "kernel. At depth m+1, splitting a word into the empty word or an "
                            + "initial input followed by a word of length at most m gives the "
                            + "kernel intersected with every successor-pair preimage.")),
                    Paragraph(Text(
                        "Repository search found and reuses runWord and "
                            + "boundedWordEquivalent from the frozen controlled behavior "
                            + "modules. Pinned Mathlib search found Set.ext, Set.mem_iInter, and "
                            + "Set.mem_preimage. No packaged theorem containing both recursion "
                            + "clauses was found."))),
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

    private static Formula RecursionFormula()
    {
        Formula states = F.Id("Y");
        Formula inputs = F.Id("U");
        Formula outputs = F.Id("O");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula depth = F.Id("m");
        Formula zero = D(0);
        Formula one = D(1);
        Formula input = F.Id("u");
        Formula kernel = Call("ker", readout);
        Formula relationZero = Call("R", update, readout, zero);
        Formula relationDepth = Call("R", update, readout, depth);
        Formula relationNext = Call("R", update, readout, Seq(depth, Plus, one));
        Formula pairMap = Call("pairMap", Call("F", input), Call("F", input));
        Formula preimage = Call("preimage", pairMap, relationDepth);
        Formula allInputs = Call("iInter", Seq(input, Sp, InMacro, Sp, inputs), preimage);

        return Disp(Seq(
            Forall, Sp, states, Comma, Sp, inputs, Comma, Sp, outputs, Comma, Esc,
            update, Colon, Sp, inputs, Sp, To, Sp, states, Sp, To, Sp, states,
            Comma, Sp, readout, Colon, Sp, states, Sp, To, Sp, outputs,
            Comma, Sp, depth, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            relationZero, Sp, Eq, Sp, kernel, Sp, Land, Esc,
            relationNext, Sp, Eq, Sp,
            Call("inter", kernel, allInputs), Dot));
    }
}
