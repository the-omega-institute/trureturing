using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class PonciniRasmussenNineHornerPart04Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHo"
                +
                "rnerPart04.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer Horner recurrence 4", H("Integer Horner recurrence 4"), Blocks(
            Paragraph(Text("The state function and coefficient list are fixed integer " +
                "data. Each equality uses the literal sparseHamiltonian " +
                "callback and the Boolean comparison of Fin.val with the " +
                "identity coordinate 4861.")),
            Node("step16", Eq(Fn("i", Fin(D(8192)),
                Add(Call("sparseHamiltonian", Call("state", D(16)), X("i")),
                    If(Call("BEq.beq", Val(X("i")), D(4861)), D(1188246329388), D(0)))),
                Call("state", D(17))),
                "This equality holds as a function on Fin 8192.", DescribeRole.Theorem),
            Node("step17", Eq(Fn("i", Fin(D(8192)),
                Add(Call("sparseHamiltonian", Call("state", D(17)), X("i")),
                    If(Call("BEq.beq", Val(X("i")), D(4861)), D(0), D(0)))),
                Call("state", D(18))),
                "This equality holds as a function on Fin 8192.", DescribeRole.Theorem),
            Node("step18", Eq(Fn("i", Fin(D(8192)),
                Add(Call("sparseHamiltonian", Call("state", D(18)), X("i")),
                    If(Call("BEq.beq", Val(X("i")), D(4861)), D(-10605723426434), D(0)))),
                Call("state", D(19))),
                "This equality holds as a function on Fin 8192.", DescribeRole.Theorem),
            Node("step19", Eq(Fn("i", Fin(D(8192)),
                Add(Call("sparseHamiltonian", Call("state", D(19)), X("i")),
                    If(Call("BEq.beq", Val(X("i")), D(4861)), D(0), D(0)))),
                Call("state", D(20))),
                "This equality holds as a function on Fin 8192.", DescribeRole.Theorem))));


    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/poncini2023planar");
    private static Formula X(string name) => F.Id(name);

    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((s, i) =>
        i == 0 ? new[] { NamePart(s) } : new[] { Dot, NamePart(s) }).ToArray());
    private static Formula NamePart(string name)
    {
        bool prime = name.EndsWith('\'');
        var words = name.Replace("'", "").Split('_');
        Formula result = F.Id(words[^1]);
        for (int i = words.Length - 2; i >= 0; --i)
            result = Seq(F.Id(words[i]), Underscore, Grp(result));
        return prime ? Seq(Operatorname, Grp(result), Apos) : Seq(Operatorname, Grp(result));
    }

    private static Formula Call(string name, params Formula[] args) => At(Q(name), args);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula D(long n) => n < 0 ? Negate(D(-n)) : Num(n);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula f, Formula type) =>
        Parenthesized(Seq(f, Colon, Sp, type));
    private static Formula Bound(string name, Formula type) => Typed(X(name), type);
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Bound(name, type), Sp, Mapsto, Sp, body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Negate(Formula a) => Seq(Minus, Parenthesized(a));
    private static Formula If(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static DocumentBlock Node(string name, Formula formula, string prose,
        DescribeRole role = DescribeRole.Definition, bool literature = false,
        bool acknowledgeSource = false) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) :
                acknowledgeSource ? AssessedProvenance.FromRepo(Source) :
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

}
