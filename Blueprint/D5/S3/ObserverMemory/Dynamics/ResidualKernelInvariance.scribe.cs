using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Dynamics;

internal sealed class ResidualKernelInvarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjoint invariance of an observable subspace preserves its orthogonal residual.",
        H("Residual Kernel Invariance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("adjoint-invariance-preserves-the-orthogonal-residual"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Dynamics/ResidualKernelInvariance."
                    + "residual_kernel_invariant"),
                H("Adjoint invariance preserves the orthogonal residual"),
                StatementSource.FromAuthor(ResidualKernelInvarianceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be a complete real or complex inner-product space, let T be a "
                        + "continuous linear endomorphism, and let S be a subspace. If the "
                        + "adjoint of T maps S into S, then T maps the orthogonal complement "
                        + "of S into itself.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies the exact general result "
                        + "ContinuousLinearMap.orthogonal_mem_invtSubmodule. The Lean proof "
                        + "translates setwise preservation into invariant-submodule membership, "
                        + "applies that result, and translates back. Loogle's exact-name query "
                        + "returned the declaration as its single hit; the repository's local "
                        + "phrase search returned no declaration-name hit.")),
                    Paragraph(Text(
                        "This covers only the orthogonal-complement step inside qdo-v1 "
                        + "theorem/28.22, atom qdo-residual-7e47cd0779d95fbf6cd811d632df7529469"
                        + "39c179a0ae2d17371fdc9d5b6d0e5. It does not assert the filtration "
                        + "equivalence, reducing invariance of every shell or final residual, "
                        + "or vanishing of all off-diagonal blocks."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula>
        {
            Operatorname,
            Grp(F.Id(name)),
            Open,
        };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula ResidualKernelInvarianceFormula()
    {
        Formula scalar = F.Id("k");
        Formula space = F.Id("E");
        Formula evolution = F.Id("T");
        Formula observable = F.Id("S");
        Formula adjoint = Call("adjoint", evolution);
        Formula residual = Seq(observable, Caret, Grp(Perp));

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, space, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("RCLike")), Open, scalar, Close,
            CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("CompleteInnerProductSpace")),
            Underscore, Grp(scalar), Open, space, Close, CloseBracket, Comma, Esc,
            evolution, Colon, Sp, Call("ContinuousLinearEnd", scalar, space), Comma, Esc,
            observable, Colon, Sp, Call("Submodule", scalar, space), Comma, Esc,
            Call("map", adjoint, observable), Sp, Subseteq, Sp, observable, Sp,
            Rightarrow, Sp,
            Call("map", evolution, residual), Sp, Subseteq, Sp, residual, Dot));
    }
}
