using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693;

internal sealed class HardinA229693StripCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion.";
    private const string Note = "D5/L/SpinModels/hardin2013a229693";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Enumerate row completions that spend exactly a given budget.",
        H("Exact-cost row completions"), Blocks(
            Node("matchCost", "Cost of a colour match",
                Arrow(Call("Option", Fin3), Arrow(Fin3, V("Nat"))),
                "An absent colour costs zero. A present colour costs one exactly when it agrees with the current colour.", DescribeRole.Definition),
            Node("completionCost", "Cost of a completion",
                ForEach("k", V("Nat"), Arrow(Boundary, Arrow(Call("Option", Fin3), Arrow(Row, V("Nat"))))),
                "Sum the initial match, when a previous colour is supplied, the matches between neighbours, and the matches against the optional boundary colours.", DescribeRole.Definition),
            Node("completionRows", "Pruned completion list",
                ForEach("k", V("Nat"), Arrow(Boundary, Arrow(Call("Option", Fin3), Arrow(V("Nat"), Call("List", Row))))),
                "Try the three available colours in order, keep each head whose cost fits the budget, and prepend it to the completions at the remaining budget. The last cell must spend the entire remaining budget.", DescribeRole.Definition),
            Node("completionRows_count", "Multiplicity of qualifying rows",
                ForEach("k", V("Nat"), ForEach("p", Boundary, ForEach("b", Call("Option", Fin3),
                    ForEach("d", V("Nat"), ForEach("f", Arrow(Row, V("Bool")),
                        Eq(Call("List.countP", V("f"), Call("completionRows", V("p"), V("b"), V("d"))),
                            Seq(Sum, Underscore, Grp(V("r"), Colon, Sp, Row), Sp, Group(Seq(
                                V("if"), Sp, Group(Eq(Call("completionCost", V("p"), V("b"), V("r")), V("d"))),
                                Sp, Land, Sp, Group(Eq(Call("f", V("r")), V("true"))),
                                Sp, V("then"), Sp, D(1), Sp, V("else"), Sp, D(0)))))))))),
                "The sum counts each qualifying row once.", DescribeRole.Theorem),
            Node("completionCodes", "Pruned list in base three",
                Arrow(Call("List", Call("Option", Fin3)), Arrow(Call("Option", Fin3), Arrow(V("Nat"), Call("List", V("Nat"))))),
                "Run the same recursion on a list of boundary colours. Prepending a colour x replaces the tail code c with x plus three times c.", DescribeRole.Definition),
            Node("rowCode_cons", "Code of a row with a new head",
                ForEach("k", V("Nat"), ForEach("x", Fin3, ForEach("r", Arrow(Call("Fin", V("k")), Fin3),
                    Eq(Code(Call("Fin.cons", V("x"), V("r"))), Add(Call("Fin.val", V("x")), new Formula.Binary(D(3), FormulaBinaryOperator.Multiply, Code(V("r")))))))),
                "The leading cell is the least significant digit of the code.", DescribeRole.Theorem),
            Node("completionCodes_eq", "Agreement of the two lists",
                ForEach("k", V("Nat"), ForEach("p", Boundary, ForEach("b", Call("Option", Fin3), ForEach("d", V("Nat"),
                    Eq(Call("completionCodes", Call("List.ofFn", V("p")), V("b"), V("d")),
                        Call("List.map", Seq(LambdaLower, Sp, V("r"), Sp, Mapsto, Sp, Code(V("r"))),
                            Call("completionRows", V("p"), V("b"), V("d")))))))),
                "The numeric enumerator returns the codes of the pruned completion list in the same order.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(declaration.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(role == DescribeRole.Definition ? Seq(V(declaration), Colon, Sp, formula) : formula)),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text(prose))), role);

    private static Formula Fin3 => Call("Fin", D(3));
    private static Formula Boundary => Arrow(Call("Fin", V("k")), Call("Option", Fin3));
    private static Formula Row => Arrow(Call("Fin", Add(V("k"), D(1))), Fin3);
    private static Formula Code(Formula row) => Call("Fin.val", Call("finFunctionFinEquiv", row));
    private static Formula V(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(
        Seq(name.Split('.').SelectMany((part, index) => index == 0
            ? new[] { Seq(Operatorname, Grp(V(part))) }
            : new[] { Dot, Seq(Operatorname, Grp(V(part))) }).ToArray()), [.. arguments]);
    private static Formula Group(Formula body) => Seq(Open, body, Close);
    private static Formula Arrow(Formula domain, Formula codomain) => Seq(Group(domain), Sp, To, Sp, Group(codomain));
    private static Formula ForEach(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Group(body));
    private static Formula Eq(Formula lhs, Formula rhs) => Seq(lhs, Sp, F.Eq, Sp, rhs);
    private static Formula Add(Formula lhs, Formula rhs) => new Formula.Binary(lhs, FormulaBinaryOperator.Add, rhs);
}
