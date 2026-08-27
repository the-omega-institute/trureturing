using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class ObservationRankEqualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite-dimensional readout and its two Gram compositions have the same rank.",
        H("Observation Rank Equality"),
        Blocks(Describe.Lean(
            DescribeId.Create("observation-rank-equality"),
            DeclarationHandle.Create(
                "D5/S3/Observer/Linear/ObservationRankEquality.observation_rank_equality"),
            H("Readout, state Gramian, and observable Gramian have equal rank"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The source readout map is a linear map between finite-dimensional inner-product "
                    + "spaces. Its adjoint composition on the state space and the reverse "
                    + "composition on the readout space have ranges of the same finite rank as "
                    + "the readout itself."))),
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

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula fn, params Formula[] args)
    {
        var items = new List<Formula> { fn, Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula k = F.Id("K");
        Formula x = F.Id("X");
        Formula p = F.Id("P");
        Formula readout = F.Id("M");
        Formula mapType = Call("LinearMap", k, x, p);
        Formula rank = F.Id("finrank");
        Formula rangeM = Call("range", readout);
        Formula stateGram = Call("range", Call("adjointComp", readout));
        Formula obsGram = Call("range", Call("compAdjoint", readout));
        Formula left = Seq(Apply(rank, k), Sp, stateGram);
        Formula middle = Seq(Apply(rank, k), Sp, rangeM);
        Formula right = Seq(Apply(rank, k), Sp, obsGram);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(k, Comma, Sp, x, Comma, Sp, p), type), Comma, RowBreak, Grp(),
            OpenBracket, Call("RCLike", k), CloseBracket, Comma, Sp,
            OpenBracket, Call("NormedAddCommGroup", x), CloseBracket, Comma, Sp,
            OpenBracket, Call("InnerProductSpace", k, x), CloseBracket, Comma, Sp,
            OpenBracket, Call("NormedAddCommGroup", p), CloseBracket, Comma, Sp,
            OpenBracket, Call("InnerProductSpace", k, p), CloseBracket, Comma, RowBreak, Grp(),
            OpenBracket, Call("FiniteDimensional", k, x), CloseBracket, Comma, Sp,
            OpenBracket, Call("FiniteDimensional", k, p), CloseBracket, Comma, RowBreak, Grp(),
            Typed(readout, mapType), Sp, Rightarrow, RowBreak, Grp(),
            left, Sp, Eq, Sp, middle, Sp, Land, Sp, middle, Sp, Eq, Sp, right, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
