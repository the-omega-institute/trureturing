using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJ2ComponentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2Components.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six actual complete path components partition the full independently defined F2 domain.",
        H("The Complete Actual J2 Component Partition"),
        Blocks(PortDefinition("componentStartPort", "The Six Independently Specified Starting Ports",
                "In index order zero through five, the starts are R0, L0, R1, L2, bar R0, and L1.", false),
            PortDefinition("componentFinishPort", "The Six Independently Specified Finishing Ports",
                "In the same order, the finishes are R2, bar L1, bar L2, bar R2, bar R1, and bar L0.", true),
            Describe.Lean(DescribeId.Create("native-j2-six-component-partition"),
            DeclarationHandle.Create(Prefix + "native_j2_six_component_partition"),
            H("Every Actual F2 Vertex Lies in Exactly One of Six Components"),
            StatementSource.FromAuthor(ComponentFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every m at least five, there is a dependent family of six actual surviving "
                + "walks with independently specified starts and finishes. Every walk is a simple "
                + "path and exhausts exactly its reachable component, including every actual edge "
                + "incident to that component. A configuration lies in F2Domain(m) exactly when "
                + "it belongs to the support of a unique member of this family.")),
                Paragraph(Text(
                "The endpoint table, in index order zero through five, is R0 to R2, L0 to bar L1, "
                + "R1 to bar L2, L2 to bar R2, bar R0 to bar R1, and L1 to bar L0. "
                + "These ports are defined independently of every path. The first five actual "
                + "walks come from the complete literal words, and the sixth comes from the "
                + "actual remaining six-cut slice. Every slice has a marked port at its start; "
                + "the complete twelve-port endpoint table connects that slice to one of the six "
                + "stated paths. Full component support then earns domain coverage. If a vertex "
                + "belonged to two supports, reachability would put one independent starting "
                + "port inside the other simple path. Its graph-leaf property forces it to be "
                + "one of that path's endpoints. Actual port injectivity and the independent "
                + "endpoint table force the two indices to be equal."))), DescribeRole.Theorem))));

    private static Formula ComponentFormula()
    {
        Formula m = F.Id("m"), paths = F.Id("paths"), i = F.Id("i");
        Formula x = F.Id("x"), y = F.Id("y"), graph = Call("survivingGraph", m);
        Formula Path(Formula index) => Call("apply", paths, index);
        Formula Start(Formula index) => Call("port", m, Call("componentStartPort", index));
        Formula Reach(Formula vertex) => Call("Reachable", graph, Start(i), vertex);
        Formula vertices = All("i", Call("Fin", D(6)), All("x", Call("Configuration", m),
            Iff(Call("Member", x, Call("Support", Path(i))), Reach(x))));
        Formula edges = All("i", Call("Fin", D(6)), All("x", Call("Configuration", m),
            All("y", Call("Configuration", m), Iff(And(Call("Adj", graph, x, y), Reach(x)),
                Call("Member", Call("Sym2Pair", x, y), Call("Edges", Path(i)))))));
        Formula j = F.Id("j");
        Formula unique = Some("i", Call("Fin", D(6)),
            And(Call("Member", x, Call("Support", Path(i))), All("j", Call("Fin", D(6)),
                Implies(Call("Member", x, Call("Support", Path(j))), Eq(j, i)))));
        Formula cover = All("x", Call("Configuration", m), Iff(Call("F2Domain", m, x), unique));
        Formula family = Call("DependentWalkFamily", Call("Fin", D(6)), graph,
            Call("componentStartPort"), Call("componentFinishPort"), m);
        Formula body = Some("paths", family,
            And(All("i", Call("Fin", D(6)), Call("IsPath", Path(i))), And(vertices, And(edges, cover))));
        return Disp(All("m", Call("Nat"), Implies(Le(D(5), m), body)));
    }

    private static DocumentBlock PortDefinition(string selector, string title, string meaning, bool finish)
    {
        Formula i = F.Id("i");
        Formula Port(byte owner, bool complemented, bool left) =>
            Call("Tuple3", D(owner), Call(complemented ? "True" : "False"), Call(left ? "True" : "False"));
        Formula[] values = finish
            ? [Port(2, false, false), Port(1, true, true), Port(2, true, true),
                Port(2, true, false), Port(1, true, false), Port(0, true, true)]
            : [Port(0, false, false), Port(0, false, true), Port(1, false, false),
                Port(2, false, true), Port(0, true, false), Port(1, false, true)];
        Formula table = values[5];
        for (byte index = 5; index > 0; index--)
            table = Call("IfThenElse", Eq(Call("FinValue", i), D((byte)(index - 1))), values[index - 1], table);
        return Describe.Lean(DescribeId.Create(finish
                ? "native-j2-component-finish-port" : "native-j2-component-start-port"),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.FromAuthor(Disp(All("i", Call("Fin", D(6)), Eq(Call(selector, i), table)))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(meaning))), DescribeRole.Definition);
    }

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
}
