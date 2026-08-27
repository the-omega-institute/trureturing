using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PredictionDepth;

internal sealed class LocalDynamicsNoTomographyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Heisenberg dynamics preserving the two local sectors cannot generate a nonzero cross-factor correlation direction.",
        H("Local Dynamics Do Not Complete Tomography"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-dynamics-no-tomography"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/PredictionDepth/LocalDynamicsNoTomography."
                        + "local_dynamics_no_tomography"),
                H("Local-sector closure excludes nonzero correlation readouts"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite bipartite Hermitian carrier is split into the canonical A-local, "
                            + "B-local, and correlation sectors.")),
                    Paragraph(Text(
                        "For any Heisenberg linear dynamics that preserves the join of the two "
                            + "local sectors, every finite iterate remains local. Orthogonality of "
                            + "the correlation sector then forces any iterate lying in it to be zero."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
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
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula t = F.Id("t");
        Formula x = F.Id("x");
        Formula nat = Seq(Operatorname, Grp(F.Id("Nat")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula carrier = Call("BipartiteHermitian", m, n);
        Formula local = Call("localASector", m, n);
        Formula localB = Call("localBSector", m, n);
        Formula localJoin = Call("Sup", local, localB);
        Formula corr = Call("correlationSector", m, n);
        Formula iter = Seq(F.Id("H"), Caret, Grp(t), Sp, x);
        Formula hlocal = Seq(
            Open, Forall, Sp, Typed(x, carrier), Comma, Sp,
            x, Sp, InMacro, Sp, localJoin, Sp, Rightarrow, Sp,
            Apply(F.Id("H"), x), Sp, InMacro, Sp, localJoin, Close);
        Formula first = Seq(Forall, Sp, Typed(t, nat), Comma, Sp,
            Typed(x, carrier), Comma, Sp,
            x, Sp, InMacro, Sp, localJoin,
            Sp, Rightarrow, Sp, Seq(iter, Sp, InMacro, Sp, localJoin));
        Formula second = Seq(Forall, Sp, Typed(t, nat), Comma, Sp,
            Typed(x, carrier), Comma, Sp,
            x, Sp, InMacro, Sp, localJoin,
            Sp, Rightarrow, Sp, Seq(iter, Sp, InMacro, Sp, corr, Sp, Rightarrow, Sp,
                iter, Sp, Eq, Sp, D(0)));
        return Disp(Seq(
            Forall, Sp, Typed(m, nat), Comma, Sp,
            Typed(n, nat), Comma, Sp,
            Call("NeZero", m), Comma, Sp,
            Call("NeZero", n), Comma, Sp,
            Typed(F.Id("H"), Call("LinearMap", real, carrier, carrier)), Comma, Sp,
            hlocal, Sp, Rightarrow, Sp,
            Open, first, Sp, Land, Sp, second, Close, Dot));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
}
