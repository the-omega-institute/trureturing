using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Trajectories;

internal sealed class CompletionKernelIntersectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The completion kernel is the intersection of all iterated readout-kernel pullbacks.",
        H("Completion Kernel Intersection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("completion-kernel-is-the-iterated-kernel-intersection"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Trajectories/CompletionKernelIntersection."
                        + "completion_kernel_eq_iterated_pullback_intersection"),
                H("The completion kernel is the intersection of iterated pullbacks"),
                StatementSource.FromAuthor(KernelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F update a state type X and let q read states into B. The "
                            + "canonical completeItinerary is constructed from these two source "
                            + "primitives by recording q after every finite iterate of F.")),
                    Paragraph(Text(
                        "The left side is displayed as the equality kernel of that canonical "
                            + "itinerary. The right side intersects, over every natural n, the "
                            + "preimage of the equality kernel of q under the paired map whose "
                            + "two coordinates are both the n-th iterate of F.")),
                    Paragraph(Text(
                        "Equality of itineraries is equality at every coordinate. Applying "
                            + "congrArg at each coordinate proves one direction, and function "
                            + "extensionality proves the other.")),
                    Paragraph(Text(
                        "Repository search found the canonical completeItinerary and the "
                            + "supporting finite-future intersection family, but no exact theorem "
                            + "packaging this completion-kernel identity. Pinned Mathlib supplies "
                            + "Setoid.ker, set preimages and intersections, Prod.map, and function "
                            + "iteration."))),
                DescribeRole.Theorem))));

    private static Formula KernelFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("B");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula pair = F.Id("p");
        Formula time = F.Id("n");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula pairType = Seq(stateType, Sp, Times, Sp, stateType);
        Formula first = Call("fst", pair);
        Formula second = Call("snd", pair);
        Formula completion = Call("completeItinerary", update, readout);
        Formula completionKernel = new Formula.SetBuilder(
            Seq(
                new Formula.Apply(completion, [first]), Sp, Eq, Sp,
                new Formula.Apply(completion, [second])),
            pair,
            pairType);
        Formula readoutKernel = new Formula.SetBuilder(
            Seq(
                new Formula.Apply(readout, [first]), Sp, Eq, Sp,
                new Formula.Apply(readout, [second])),
            pair,
            pairType);
        Formula iterate = new Formula.Power(Seq(update), Seq(time));
        Formula pairedIterate = Seq(
            Operatorname, Grp(Seq(F.Id("Prod"), Dot, F.Id("map"))),
            Open, iterate, Comma, Sp, iterate, Close);
        Formula pullback = Call("preimage", pairedIterate, readoutKernel);
        Formula intersection = Seq(
            Operatorname, Grp(F.Id("intersection")),
            Underscore, Grp(Seq(time, Sp, InMacro, Sp, naturals)),
            Sp, pullback);

        return Disp(Seq(
            Forall, Sp, stateType, Comma, Sp, outputType,
            Colon, Sp, type, Comma, Esc,
            update, Colon, Sp, new Formula.TypeArrow(stateType, stateType), Comma, Sp,
            readout, Colon, Sp, new Formula.TypeArrow(stateType, outputType), Comma, Esc,
            completionKernel, Sp, Eq, Sp, intersection, Dot));
    }
}
