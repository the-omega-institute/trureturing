using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeCircleTerminalEdgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleTerminalEdge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed last label determines exactly one undirected b edge in an actual complete native circle.",
        H("Unique Native b Edge at a Fixed Last Label"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-circle-same-last-iff"),
                DeclarationHandle.Create(Prefix + "native_circle_same_last_iff"),
                H("Exactly Two Circle Orientations Have the Anchor's Last Label"),
                StatementSource.FromAuthor(SameLastFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every m at least three, every actual anchor z and every "
                    + "configuration x in its complete rotation/reversal circle, "
                    + "x and z have the same last label exactly when x=z or x=zb. "
                    + "The actual circle equivalence supplies rotation/reflection "
                    + "coordinates. In positive orientation the equal last label "
                    + "forces rotation zero. In negative orientation it forces the "
                    + "last rotation index, which is minus one; the existing actual "
                    + "identity b=finCycle(-1)*a identifies the second orientation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-circle-terminal-b-edge"),
                DeclarationHandle.Create(Prefix + "native_circle_terminal_b_edge"),
                H("All Such Orientations Give the Same Undirected b Edge"),
                StatementSource.FromAuthor(EdgeFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If x belongs to the actual circle of z and has z's last label, "
                    + "the undirected b edge from x to xb is exactly the edge from "
                    + "z to zb. The preceding orientation classification gives "
                    + "x=z or x=zb; b squared is the identity, so the second case "
                    + "only exchanges the two endpoints. The result is independent "
                    + "of any chosen complement path or Hamilton cycle."))),
                DescribeRole.Theorem))));

    private static Formula SameLastFormula()
    {
        Formula m = F.Id("m"), z = F.Id("z"), x = F.Id("x");
        return Quantified(m, z, x, Implies(Call("Circle", z, x),
            new Formula.Logic(Eq(Call("LastLabel", m, x), Call("LastLabel", m, z)),
                FormulaLogicOperator.Iff, new Formula.Logic(Eq(x, z), FormulaLogicOperator.Or,
                    Eq(x, Call("Mul", z, Call("b", m)))))));
    }

    private static Formula EdgeFormula()
    {
        Formula m = F.Id("m"), z = F.Id("z"), x = F.Id("x");
        return Quantified(m, z, x, Implies(new Formula.Logic(Call("Circle", z, x),
            FormulaLogicOperator.And, Eq(Call("LastLabel", m, x), Call("LastLabel", m, z))),
            Eq(Call("Sym2Pair", x, Call("Mul", x, Call("b", m))),
                Call("Sym2Pair", z, Call("Mul", z, Call("b", m))))));
    }

    private static Formula Quantified(Formula m, Formula z, Formula x, Formula body) =>
        Disp(All("m", Call("Nat"), Implies(Le(D(3), m), All("z", Call("Configuration", m),
            All("x", Call("Configuration", m), body)))));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
