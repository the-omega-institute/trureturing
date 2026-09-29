using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class ResponseOrderGraphDistanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/ResponseOrderGraphDistance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive off-diagonal couplings first appear at the graph distance.",
        H("Response Order and Graph Distance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coupling-graph"),
                DeclarationHandle.Create(Prefix + "couplingGraph"),
                H("The coupling graph"),
                StatementSource.FromAuthor(GraphFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The graph joins distinct vertices whenever the corresponding coupling entry is positive."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("first-nonzero-power"),
                DeclarationHandle.Create(Prefix + "first_nonzero_power_eq_graph_distance"),
                H("The first nonzero power is the graph distance"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a symmetric matrix whose off-diagonal entries are nonnegative, every power below the "
                    + "distance between reachable distinct vertices has zero cross-entry, while the power at that "
                    + "distance has a strictly positive cross-entry."))),
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


    private static Formula GraphFormula()
    {
        Formula h = F.Id("H"), i = F.Id("i"), j = F.Id("j");
        Formula adj = Seq(Call("couplingGraph", h), Dot, Call("Adj", i, j));
        return Disp(Seq(
            adj, Sp, Iff, Sp, i, Sp, Neq, Sp, j, Sp, Land, Sp, Open, D(0), Sp, Lt, Sp,
            h, Underscore, Grp(i, Sp, j), Sp, Lor, Sp, D(0), Sp, Lt, Sp, h, Underscore, Grp(j, Sp, i), Close, Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), h = F.Id("H"), i = F.Id("i"), j = F.Id("j"), n = F.Id("n");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula graph = Call("couplingGraph", h);
        Formula dist = Call("dist", graph, i, j);
        Formula entry(Formula a, Formula b) => Seq(h, Underscore, Grp(a, Sp, b));
        Formula powEntry(Formula k) => Seq(Grp(Seq(h, Caret, Grp(k))), Underscore, Grp(j, Sp, i));
        Formula symmetry = Seq(Forall, Sp, i, Comma, Sp, j, Comma, Sp, entry(i, j), Sp, Eq, Sp, entry(j, i));
        Formula nonneg = Seq(Forall, Sp, i, Comma, Sp, j, Comma, Sp, i, Sp, Neq, Sp, j, Sp, Rightarrow, Sp,
            D(0), Sp, Leq, Sp, entry(i, j));
        Formula early = Seq(Forall, Sp, n, Sp, Lt, Sp, dist, Comma, Sp, powEntry(n), Sp, Eq, Sp, D(0));
        Formula first = Seq(D(0), Sp, Lt, Sp, powEntry(dist));
        return Disp(Seq(
            h, Sp, InMacro, Sp, real, Caret, Grp(d, Sp, Times, Sp, d), Comma, Sp, symmetry, Comma, Sp, nonneg,
            Comma, RowBreak, Grp(),
            i, Sp, Neq, Sp, j, Comma, Sp, Call("Reachable", graph, i, j), Sp, Rightarrow, Sp,
            Open, early, Close, Sp, Land, Sp, first, Dot));
    }
}
