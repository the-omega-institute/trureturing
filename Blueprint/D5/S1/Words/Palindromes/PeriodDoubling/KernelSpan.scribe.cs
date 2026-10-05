using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class KernelSpanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/KernelSpan.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binary kernel records every power-of-two residue subsequence.", H("Rational Spans of Binary Kernels"), Blocks(
        Describe.Lean(DescribeId.Create("pd-kernelspan-twokernel"),
            DeclarationHandle.Create(Prefix + "twoKernel"), H("The literal binary kernel"),
            StatementSource.FromAuthor(KernelFormula()), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Words/fridlabordepeltomaki2021automaticppl")),
            Blocks(Paragraph(Text("This is the literal k = 2 case of the k-kernel definition in the FLP paper (Frid, Laborde and Peltomäki, On prefix palindromic length of automatic words). The binary kernel contains exactly the functions n mapped to f(2^e n+r), with e nonnegative and r strictly below 2^e. Its output carrier A is unrestricted."))), DescribeRole.Definition))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula Fn(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);


    private static Formula KernelFormula()
    {
        var sequence = Lam("n", N(), At(V("f"), Add(Mul(Pow(D(2), V("e")), V("n")), V("r"))));
        var address = Ex("e", N(), Ex("r", N(), And(LtF(V("r"), Pow(D(2), V("e"))),
            Eqn(V("g"), sequence))));
        var set = Seq(OpenBrace, V("g"), Colon, Fn(N(), V("A")), Sp, Mid, Sp, address, CloseBrace);
        return Disp(All("A", Ty("Type"), All("f", Fn(N(), V("A")),
            Eqn(Call("twoKernel", V("f")), set))));
    }
}
