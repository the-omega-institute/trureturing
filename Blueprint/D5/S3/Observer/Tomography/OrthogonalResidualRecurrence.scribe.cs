using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Tomography;

internal sealed class OrthogonalResidualRecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recursive orthogonal extraction splits each residual and the ambient Hilbert space.",
        H("Orthogonal Residual Recurrence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("recursive-orthogonal-extraction-splits-residuals"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Tomography/OrthogonalResidualRecurrence."
                        + "orthogonal_residual_recurrence"),
                H("Recursive orthogonal extraction splits residuals"),
                StatementSource.FromAuthor(ResidualRecurrenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let H be a complete real inner-product space, let M be a closed "
                            + "subspace, and let E be a sequence of closed shells. Construct "
                            + "the accumulated tower from joins with E(n+1), and independently "
                            + "construct the residual tower from intersections with the "
                            + "orthogonal complements of E(n+1).")),
                    Paragraph(Text(
                        "If every next shell lies in the current residual, then the next "
                            + "residual is the orthogonal complement of the next accumulated "
                            + "space. The current residual is the orthogonal direct sum of the "
                            + "next shell and next residual, and the ambient space is the "
                            + "orthogonal direct sum of the next accumulated space and residual.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle returned ClosedSubmodule.inf_orthogonal and "
                            + "Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection as exact "
                            + "one-step identities. The Lean proof applies both directly."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[i]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula Indexed(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Successor(Formula index) => Seq(index, Plus, D(1));

    private static Formula Orthogonal(Formula value) => Seq(value, Caret, Grp(Perp));

    private static Formula Join(Formula left, Formula right) => Call("join", left, right);

    private static Formula IsOrtho(Formula left, Formula right) => Call("IsOrtho", left, right);

    private static Formula ResidualRecurrenceFormula()
    {
        Formula h = F.Id("H");
        Formula m = F.Id("M");
        Formula e = F.Id("E");
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula nextN = Successor(n);
        Formula nextK = Successor(k);
        Formula sN = Call("accumulatedSubspace", m, e, nextN);
        Formula rN = Call("recursiveResidual", m, e, n);
        Formula rNext = Call("recursiveResidual", m, e, nextN);
        Formula shell = Indexed(e, nextN);

        return Disp(Seq(
            Forall, Sp, h, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("NormedAddCommGroup")), Open, h, Close,
            CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("InnerProductSpace")), Open,
            Mathbb, Grp(F.Id("R")), Comma, Sp, h, Close, CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("CompleteSpace")), Open, h, Close,
            CloseBracket, Comma, Esc,
            Forall, Sp, m, Colon, Sp, Call("ClosedSub", real, h),
            Comma, Sp, e, Colon, Sp, Mathbb, Grp(F.Id("N")), Sp, To, Sp,
            Call("ClosedSub", real, h), Comma, Esc,
            Open, Forall, Sp, k, Comma, Sp, Indexed(e, nextK), Sp, Subseteq, Sp,
            Call("recursiveResidual", m, e, k), Close, Sp, Rightarrow, Sp,
            Forall, Sp, n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            rNext, Sp, Eq, Sp, Orthogonal(sN), Sp, Land, RowBreak,
            IsOrtho(shell, rNext), Sp, Land, Sp, rN, Sp, Eq, Sp,
            Join(shell, rNext), Sp, Land, RowBreak,
            IsOrtho(sN, rNext), Sp, Land, Sp,
            Operatorname, Grp(F.Id("top")), Sp, Eq, Sp, Join(sN, rNext), Dot));
    }
}
