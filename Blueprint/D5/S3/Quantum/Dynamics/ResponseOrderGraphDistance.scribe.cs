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

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula And(Formula left, Formula right) => Seq(left, Sp, Land, Sp, right);
    private static Formula BindAll(Formula variable, Formula body) =>
        Seq(Forall, Sp, variable, Comma, Sp, body);
    private static Formula Power(Formula value, Formula exponent) =>
        Seq(Grp(value), Caret, Grp(exponent));

    private static Formula GraphFormula()
    {
        Formula d = F.Id("d"), h = F.Id("H");
        Formula fin = Call("Fin", d);
        Formula matrix = Call("Matrix", fin, fin, Mathbb, Grp(F.Id("R")));
        Formula graph = Call("SimpleGraph", fin);
        return Disp(Seq(
            Forall, Sp, Typed(d, Operatorname), Comma, Sp,
            Typed(h, matrix), Sp, Rightarrow, Sp,
            Typed(Call("couplingGraph", h), graph), Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), h = F.Id("H"), i = F.Id("i"), j = F.Id("j"), n = F.Id("n");
        Formula fin = Call("Fin", d);
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula matrix = Call("Matrix", fin, fin, real);
        Formula graph = Call("couplingGraph", h);
        Formula dist = Call("dist", graph, i, j);
        Formula symmetry = BindAll(i, BindAll(j,
            Seq(h, Underscore, Grp(i), j, Sp, Eq, Sp, h, Underscore, Grp(j), i)));
        Formula nonneg = BindAll(i, BindAll(j, Seq(i, Neq, j, Sp, Rightarrow, Sp,
            D(0), Sp, Le, Sp, h, Underscore, Grp(i), j)));
        Formula early = BindAll(n, Seq(n, Lt, dist, Sp, Rightarrow, Sp,
            Power(h, n), Sp, j, Sp, i, Sp, Eq, Sp, D(0)));
        Formula first = Seq(D(0), Sp, Lt, Sp, Power(h, dist), Sp, j, Sp, i);
        return Disp(Seq(
            Forall, Sp, Typed(d, Operatorname), Comma, Sp,
            Typed(h, matrix), Comma, Sp, symmetry, Comma, Sp, nonneg, Comma, Sp,
            Typed(i, fin), Comma, Sp, Typed(j, fin), Comma, Sp, i, Neq, j, Comma, Sp,
            Call("Reachable", graph, i, j), Sp, Rightarrow, RowBreak, Grp(),
            And(early, first), Dot));
    }
}
