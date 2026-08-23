using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Tomography;

internal sealed class RecursiveCompletenessCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Terminal residual vanishing characterizes complete recursive Hilbert decomposition.",
        H("Recursive Completeness Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("terminal-residual-characterizes-recursive-completeness"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Tomography/RecursiveCompletenessCriterion."
                        + "recursive_completeness_criterion"),
                H("Terminal residual characterizes recursive completeness"),
                StatementSource.FromAuthor(CompletenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let H be a complete real Hilbert space, M a closed initial subspace, "
                            + "and E a sequence of closed shells. The accumulated tower and "
                            + "residual tower are imported from the canonical recurrence family. "
                            + "The terminal accumulated space is their finite-stage supremum, "
                            + "while the terminal residual is the intersection of all residuals.")),
                    Paragraph(Text(
                        "If each next shell lies in the current recursively constructed residual, "
                            + "then terminal residual zero, terminal accumulated space equal to "
                            + "the ambient space, and the closed expansion of M with every shell "
                            + "equal to the ambient space are equivalent.")),
                    Paragraph(Text(
                        "In the complete case, M and all shells form an exact Hilbert sum. In the "
                            + "incomplete case, adjoining the terminal residual gives the exact "
                            + "Hilbert sum, and every vector in that residual is orthogonal to M "
                            + "and to every selected shell. This is the formal never-named sector.")),
                    Paragraph(Text(
                        "Pinned library search found the exact infinite-intersection orthogonal "
                            + "identity and the internal Hilbert-sum constructor. The Lean proof "
                            + "applies them to the imported recursive residual semantics."))),
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

    private static Formula Indexed(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Successor(Formula index) => Seq(index, Plus, D(1));

    private static Formula Orthogonal(Formula value) => Seq(value, Caret, Grp(Perp));

    private static Formula CompletenessFormula()
    {
        Formula h = F.Id("H");
        Formula m = F.Id("M");
        Formula e = F.Id("E");
        Formula n = F.Id("n");
        Formula x = F.Id("x");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula next = Successor(n);
        Formula shell = Indexed(e, next);
        Formula residualAtN = Call("recursiveResidual", m, e, n);
        Formula terminalResidual = Call("terminalResidual", m, e);
        Formula terminalAccumulated = Call("terminalAccumulated", m, e);
        Formula expansion = Call("shellExpansion", m, e);
        Formula knownFamily = Call("knownShellFamily", m, e);
        Formula fullFamily = Call("fullShellFamily", m, e);
        Formula top = Call("top");
        Formula bottom = Call("bot");

        return Disp(Seq(
            Forall, Sp, h, Colon, Sp, Call("CompleteRealHilbertSpace", h), Comma, Esc,
            Forall, Sp, m, Colon, Sp, Call("ClosedSub", real, h), Comma, Sp,
            e, Colon, Sp, natural, Sp, To, Sp, Call("ClosedSub", real, h), Comma, Esc,
            Open, Forall, Sp, n, InMacro, Sp, natural, Comma, Sp,
            shell, Sp, Subseteq, Sp, residualAtN, Close, Sp, Rightarrow, RowBreak,
            Open,
            Open, terminalResidual, Sp, Eq, Sp, bottom, Sp, Leftrightarrow, Sp,
            terminalAccumulated, Sp, Eq, Sp, top, Close, Sp, Land, RowBreak,
            Open, terminalAccumulated, Sp, Eq, Sp, top, Sp, Leftrightarrow, Sp,
            expansion, Sp, Eq, Sp, top, Close, Sp, Land, RowBreak,
            Open, terminalResidual, Sp, Eq, Sp, bottom, Sp, Rightarrow, Sp,
            Call("IsHilbertSum", knownFamily), Close, Sp, Land, RowBreak,
            Open, terminalResidual, Sp, Neq, Sp, bottom, Sp, Rightarrow, Sp,
            Open, Call("IsHilbertSum", fullFamily), Sp, Land, RowBreak,
            Forall, Sp, x, Comma, Sp, x, InMacro, Sp, terminalResidual, Sp,
            Rightarrow, Sp, Open, x, InMacro, Sp, Orthogonal(m), Sp, Land, Sp,
            Forall, Sp, n, InMacro, Sp, natural, Comma, Sp,
            x, InMacro, Sp, Orthogonal(shell), Close,
            Close, Close, Close, Dot));
    }
}
