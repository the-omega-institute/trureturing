using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class JenzerPermutedRotorLoopDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/JenzerPermutedRotorLoop.";
    private const string Note = "D5/L/QuadraticForms/jenzer2026starorderedrotorloops";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Permuted rotor loops obey the subset formula without the star condition.", H("JenzerPermutedRotorLoop"),
        Blocks(
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"), H("Permuted rotor loops without the star condition"),
                StatementSource.FromAuthor(Disp(Formula0())), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Anticommuting conjugations remove all off-diagonal scalar terms except possible odd full support. The top coefficient of the balanced exterior word cancels that aggregate. The remaining diagonal terms give the full subset formula for every source signature, angle and permutation. No nonzero sine or cosine assumption is used."))), DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("jen2610"), ResolutionKind.Proved)))));

    private static Formula Formula0() => All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", Real, X("V")), Instance(Call("FiniteDimensional", Real, X("V")), All(X("q"), Call("QuadraticForm", Real, X("V")), ImpliesFormula(Member(X("q"), "Nondegenerate"), All(X("k"), Nat, ImpliesFormula(LessEqual(D(1), X("k")), All(X("B"), Arrow(Call("Fin", X("k")), Call("CliffordAlgebra", X("q"))), ImpliesFormula(Call("AnticommutingUnitFamily", X("q"), X("k"), X("B")), All(X("theta"), Arrow(Call("Fin", X("k")), Real), All(X("tau"), Call("Equiv.Perm", Call("Fin", X("k"))), Equal(Call("scalarProjection", X("q"), Call("loop", X("B"), X("theta"), X("tau"))), Summation(X("S"), Member(Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k")))), "powerset"), Multiply(Multiply(Multiply(Call("eta", Member(X("S"), "card")), Power(Cast(Negative(D(1)), Real), Call("inversionCount", X("tau"), X("S")))), Product(X("i"), X("S"), Call("w", X("theta"), X("i")))), Product(X("i"), SetDifference(Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k")))), X("S")), Subtract(D(1), Call("w", X("theta"), X("i")))))))))))))))))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Type => X("Type");
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula Real => Seq(Mathbb, Grp(X("R")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Name(string name) => Seq(name.Split('.').Select((part, index) =>
        index == 0 ? Seq(Operatorname, Grp(X(part))) : Seq(Dot, Operatorname, Grp(X(part)))).ToArray());
    private static Formula Call(string name, params Formula[] args) => App(Name(name), args);
    private static Formula App(Formula function, params Formula[] args) => args.Length == 0 ? function : new Formula.Apply(function, [.. args]);
    private static Formula Member(Formula value, string name) => Seq(Parenthesized(value), Dot, Name(name));
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp,
        Parenthesized(Seq(name, Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Arrow(Formula source, Formula target) => Parenthesized(Seq(source, Sp, To, Sp, target));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, Parenthesized(right));
    private static Formula LessEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Negative(Formula value) => Seq(Minus, Parenthesized(value));
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula ImpliesFormula(Formula premise, Formula conclusion) => new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies, Parenthesized(conclusion));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula SetDifference(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Setminus, Sp, Parenthesized(right));
    private static Formula Product(Formula name, Formula set, Formula body) => Seq(new Formula.Subscript(Prod, Seq(name, Sp, InMacro, Sp, set)), Sp, Parenthesized(body));
    private static Formula Summation(Formula name, Formula set, Formula body) => Seq(new Formula.Subscript(Sum, Seq(name, Sp, InMacro, Sp, set)), Sp, Parenthesized(body));
}
