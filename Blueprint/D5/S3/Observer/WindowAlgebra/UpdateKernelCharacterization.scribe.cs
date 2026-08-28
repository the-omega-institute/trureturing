using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WindowAlgebra;

internal sealed class UpdateKernelCharacterizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero update difference is exactly invariance, and cyclic-window fixed observables are constants.",
        H("Update Kernel and Fixed Observables"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("update-difference-kernel-fixed-observables"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/WindowAlgebra/UpdateKernelCharacterization."
                        + "update_difference_kernel_fixed_observables"),
                H("Update difference kernel and fixed observables"),
                StatementSource.FromAuthor(UpdateKernelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an update permutation tau on an observable index type, the "
                            + "update-difference map is constructed pointwise from the existing "
                            + "observer update defect. The fixed-observable submodule is constructed "
                            + "from the pointwise relation f(tau i) = f(i), rather than being defined "
                            + "from the target kernel.")),
                    Paragraph(Text(
                        "The first clause applies the existing zero-defect/invariance equivalence. "
                            + "Extensionality then identifies the linear kernel with the independently "
                            + "constructed fixed-observable submodule. On a nonempty cyclic window, "
                            + "the existing cyclic invariance theorem identifies every kernel "
                            + "observable with a constant function.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplied only the generic LinearMap.ker membership rule; "
                            + "repository search found no packaged update-kernel/fixed-submodule "
                            + "theorem. The source clauses are stated together in the public theorem "
                            + "so no clause is hidden in a private helper."))),
                DescribeRole.Theorem))));

    private static Formula UpdateMap(Formula tau) =>
        Seq(F.Id("L"), Underscore, Grp(tau));

    private static Formula UpdateKernelFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula index = F.Id("I");
        Formula tau = F.Id("tau");
        Formula observable = F.Id("f");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula permutation = Call("Perm", index);
        Formula observableType = Seq(index, Sp, To, Sp, complex);
        Formula updateMap = UpdateMap(tau);
        Formula zero = Seq(updateMap, Open, observable, Close, Sp, Eq, Sp, D(0));
        Formula invariant = Seq(
            observable, Sp, Circ, Sp, tau, Sp, Eq, Sp, observable);
        Formula kernel = Seq(Ker, Sp, updateMap);
        Formula fixedSubmodule = Seq(
            Operatorname, Sp, Grp(F.Id("Inv")), Underscore, Grp(tau));
        Formula cyclicKernel = Seq(
            F.Id("g"), Sp, InMacro, Sp,
            Seq(Ker, Sp, UpdateMap(Seq(Plus, D(1)))),
            Sp, Iff, Sp,
            Exists, Sp, F.Id("c"), InMacro, Sp,
            Mathbb, Grp(F.Id("C")), Comma, Esc,
            F.Id("g"), Sp, Eq, Sp,
            Open, F.Id("i"), Mapsto, Sp, F.Id("c"), Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, index, Colon, Sp, type, Comma, Sp,
            tau, Colon, Sp, permutation, Comma, Sp,
            observable, Colon, Sp, observableType, Comma, RowBreak,
            zero, Sp, Leftrightarrow, Sp, invariant, Semi, Sp, RowBreak,
            kernel, Sp, Eq, Sp, fixedSubmodule, Semi, Sp, RowBreak,
            Forall, Sp, F.Id("M"), Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)), Comma, Esc,
            Forall, Sp, F.Id("g"), Colon, Sp,
            Operatorname, Sp, Grp(F.Id("ZMod")), Open, F.Id("M"), Close,
            To, Sp, Mathbb, Grp(F.Id("C")), Comma, Esc,
            cyclicKernel, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
