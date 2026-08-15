using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Tomography;

internal sealed class FiniteStageExpansionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite orthogonal shell towers expand into the initial space, extracted shells, and residual.",
        H("Finite-Stage Orthogonal Expansion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-orthogonal-shell-towers-expand-stagewise"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Tomography/FiniteStageExpansion.finite_stage_expansion"),
                H("Finite orthogonal shell towers expand stagewise"),
                StatementSource.FromAuthor(FiniteStageExpansionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let H be a complete real inner-product space. Let S and E be sequences "
                            + "of closed subspaces. At each stage, S(k+1) is the join of S(k) and "
                            + "E(k+1), while E(k+1) lies in the orthogonal complement of S(k).")),
                    Paragraph(Text(
                        "For every finite stage n, S(n) is the join of S(0) with the first n "
                            + "shells. The whole space is the join of that accumulated stage and "
                            + "its orthogonal residual. The current residual is itself the join "
                            + "of the next shell and the next residual.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle returned "
                            + "Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection as the exact "
                            + "one-step splitting result, which the Lean proof imports and applies. "
                            + "Repository and library searches found no exact finite-stage "
                            + "expansion, so the shell accumulation is proved by induction.")),
                    Paragraph(Text(
                        "The closed-subspace formulation preserves arbitrary complete Hilbert "
                            + "spaces and therefore includes finite-dimensional extracted shells "
                            + "without restricting the ambient space to finite dimension."))),
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

    private static Formula FiniteStageExpansionFormula()
    {
        Formula h = F.Id("H");
        Formula s = F.Id("S");
        Formula e = F.Id("E");
        Formula k = F.Id("k");
        Formula n = F.Id("n");
        Formula zero = D(0);
        Formula one = D(1);
        Formula shellSpan = Call("finiteShellSpan", e, n);
        Formula stage = Join(Indexed(s, zero), shellSpan);

        return Disp(Seq(
            Forall, Sp, h, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("NormedAddCommGroup")), Open, h, Close,
            CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("InnerProductSpace")), Open,
            Mathbb, Grp(F.Id("R")), Comma, Sp, h, Close, CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("CompleteSpace")), Open, h, Close,
            CloseBracket, Comma, Esc,
            Forall, Sp, s, Comma, Sp, e, Colon, Sp, Mathbb, Grp(F.Id("N")), Sp, To, Sp,
            Operatorname, Grp(F.Id("ClosedSub")), Open, Mathbb, Grp(F.Id("R")), Comma,
            Sp, h, Close, Comma, Esc,
            Open, Forall, Sp, k, Comma, Sp,
            Indexed(s, Successor(k)), Sp, Eq, Sp,
            Join(Indexed(s, k), Indexed(e, Successor(k))), Close, Sp, Rightarrow, Sp,
            Open, Forall, Sp, k, Comma, Sp,
            Indexed(e, Successor(k)), Sp, Subseteq, Sp, Orthogonal(Indexed(s, k)),
            Close, Sp, Rightarrow, Sp,
            Forall, Sp, n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Indexed(s, n), Sp, Eq, Sp, stage, Sp, Land, RowBreak,
            Operatorname, Grp(F.Id("top")), Sp, Eq, Sp,
            Join(stage, Orthogonal(Indexed(s, n))), Sp, Land, RowBreak,
            Orthogonal(Indexed(s, n)), Sp, Eq, Sp,
            Join(Indexed(e, Successor(n)), Orthogonal(Indexed(s, Successor(n)))), Dot));
    }
}
