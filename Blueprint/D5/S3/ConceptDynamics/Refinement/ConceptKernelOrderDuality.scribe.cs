using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Refinement;

internal sealed class ConceptKernelOrderDualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Effective concept classes are dual to source equivalence relations.",
        H("Concept Classes and Kernel Relations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("concept-kernel-order-duality"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Refinement/ConceptKernelOrderDuality."
                        + "concept_kernel_order_duality"),
                H("Effective concept classes are order-dual to kernel relations"),
                StatementSource.FromAuthor(DualityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An effective concept presentation consists of a readout together with "
                            + "surjectivity onto its coordinate carrier. Mutual refinement is "
                            + "the antisymmetrization of the canonical factor-map preorder.")),
                    Paragraph(Text(
                        "The kernel map sends each resulting concept class to the equality "
                            + "relation induced on its source. It is publicly bijective, and a "
                            + "coarse concept refines through a finer one exactly when the finer "
                            + "kernel is contained in the coarse kernel.")),
                    Paragraph(Text(
                        "The final two public conjuncts use the canonical family join and the "
                            + "quotient projection for common coarsening. Their kernels are, "
                            + "respectively, the relation intersection and the equivalence "
                            + "closure of the relation union.")),
                    Paragraph(Text(
                        "The proof directly applies the pinned antisymmetrization and setoid "
                            + "lattice constructions. Surjectivity supplies representatives for "
                            + "the reverse kernel-to-factorization implication."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula DualityFormula()
    {
        Formula state = F.Id("X");
        Formula coarse = F.Id("C");
        Formula fine = F.Id("D");
        Formula coarseReadout = new Formula.Subscript(F.Id("q"), coarse);
        Formula fineReadout = new Formula.Subscript(F.Id("q"), fine);
        Formula kernelMap = Call("conceptClassKernel", state);
        Formula coarseKernel = Call("ker", coarseReadout);
        Formula fineKernel = Call("ker", fineReadout);
        Formula bijection = Call("Bijective", kernelMap);
        Formula reverseOrder = Seq(
            Forall, Sp, coarse, Comma, Sp, fine, Sp, InMacro, Sp,
            Call("EffectiveConcept", state), Comma, Sp,
            Call("Refines", coarseReadout, fineReadout), Sp, Iff, Sp,
            fineKernel, Sp, Subseteq, Sp, coarseKernel);
        Formula joinKernel = Seq(
            Forall, Sp, coarseReadout, Comma, Sp, fineReadout, Comma, Sp,
            Call("ker", Call("conceptJoin", coarseReadout, fineReadout)),
            Sp, Eq, Sp, Call("intersection", coarseKernel, fineKernel));
        Formula coarseningKernel = Seq(
            Forall, Sp, coarseReadout, Comma, Sp, fineReadout, Comma, Sp,
            Call("ker", Call("commonCoarsening", coarseReadout, fineReadout)),
            Sp, Eq, Sp,
            Call("EqvClosure", Call("union", coarseKernel, fineKernel)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Colon, Sp, Operatorname, Grp(F.Id("Type")),
            Comma, RowBreak, Grp(),
            bijection, Sp, Land, RowBreak, Grp(),
            Open, reverseOrder, Close, Sp, Land, RowBreak, Grp(),
            Open, joinKernel, Close, Sp, Land, RowBreak, Grp(),
            Open, coarseningKernel, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
