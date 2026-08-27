using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class CompactLocalRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite local realizability of closed records on a compact carrier yields one global realization.",
        H("Compact Local Realization"),
        Blocks(Describe.Lean(
            DescribeId.Create("compact-local-realization"),
            DeclarationHandle.Create(
                "D5/S3/Observer/Completion/CompactLocalRealization.compact_local_realization"),
            H("Finite local compatibility implies global compatibility"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For each context, the equality fiber of the continuous local record is closed. "
                    + "Every finite family of fibers is nonempty, so compactness gives a point in "
                    + "their total intersection."))),
            DescribeRole.Theorem))));

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);

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

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula x = F.Id("X");
        Formula context = F.Id("C");
        Formula record = F.Id("B");
        Formula beta = F.Id("beta");
        Formula target = F.Id("b");
        Formula finite = F.Id("s");
        Formula point = F.Id("x");
        Formula fiber = Call("fiber", beta, target);
        Formula equality = Seq(beta, Open, context, Close, Sp, point, Sp, Eq, Sp,
            target, Open, context, Close);
        Formula closed = Seq(Forall, Sp, Typed(context, F.Id("C")), Comma, Sp,
            Call("IsClosed", Call("setOf", equality)));
        Formula finiteRealizable = Seq(
            Forall, Sp, Typed(finite, Call("Finset", context)), Comma, Sp,
            Exists, Sp, point, Comma, Sp,
            Forall, Sp, Typed(context, F.Id("C")), Comma, Sp,
            context, Sp, InMacro, Sp, finite, Sp, Rightarrow, Sp,
            beta, Open, context, Comma, Sp, point, Close, Sp, Eq, Sp,
            target, Open, context, Close);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(x, Comma, Sp, context, Comma, Sp, record), type), Comma,
            RowBreak, Grp(),
            OpenBracket, Call("TopologicalSpace", x), CloseBracket, Comma, Sp,
            OpenBracket, Call("CompactSpace", x), CloseBracket, Comma, RowBreak, Grp(),
            Typed(beta, Seq(context, Sp, To, Sp, x, Sp, To, Sp, record)), Comma, Sp,
            Typed(target, Seq(context, Sp, To, Sp, record)), Comma, RowBreak, Grp(),
            closed, Comma, Sp, finiteRealizable, Sp, Rightarrow, RowBreak, Grp(),
            Exists, Sp, point, Comma, Sp, Forall, Sp,
            Typed(context, F.Id("C")), Comma, Sp, equality, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
