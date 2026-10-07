using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.HiguchiSudbery;

internal sealed class HermiteMajorantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two double contacts and a nonnegative fourth derivative force nonnegativity on the positive half-line.",
        H("HermiteMajorant"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("double-contact-nonnegative"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/HiguchiSudbery/HermiteMajorant.double_contact_nonnegative"),
                H("Fourth derivative comparison"),
                StatementSource.FromAuthor(Disp(CompareFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The functions f, f₁, f₂, f₃ and f₄ form a derivative chain at every positive point. Both f and f₁ vanish at the ordered positive nodes a and b. The displayed conclusion covers every positive x, including the contact nodes."))),
                DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula At(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Eqn(Formula lhs, Formula rhs) => new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula Leq(Formula lhs, Formula rhs) => new Formula.Relation(lhs, FormulaRelationOperator.LessThanOrEqual, rhs);
    private static Formula Less(Formula lhs, Formula rhs) => new Formula.Relation(lhs, FormulaRelationOperator.LessThan, rhs);
    private static Formula And(Formula lhs, Formula rhs) => new Formula.Logic(Parenthesized(lhs), FormulaLogicOperator.And, Parenthesized(rhs));
    private static Formula Imp(Formula lhs, Formula rhs) => new Formula.Logic(Parenthesized(lhs), FormulaLogicOperator.Implies, Parenthesized(rhs));
    private static Formula Fn(Formula lhs, Formula rhs) => new Formula.TypeArrow(lhs, rhs);
    private static Formula R => Call("Real");
    private static Formula Function(byte index) => index == 0 ? F.Id("f") : new Formula.Subscript(F.Id("f"), D(index));
    private static Formula CompareFormula()
    {
        Formula x = F.Id("x");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula guards = And(Less(D(0), a), Less(a, b));
        guards = And(guards, And(Eqn(At(Function(0), a), D(0)), Eqn(At(Function(0), b), D(0))));
        guards = And(guards, And(Eqn(At(Function(1), a), D(0)), Eqn(At(Function(1), b), D(0))));
        Formula body = All("a", R, All("b", R, Imp(guards,
            All("x", R, Imp(Less(D(0), x), Leq(D(0), At(Function(0), x)))))));
        Formula fourth = All("x", R, Imp(Less(D(0), x), Leq(D(0), At(Function(4), x))));
        body = Imp(fourth, body);
        for (byte j = 4; j > 0; j--)
        {
            byte k = (byte)(j - 1);
            body = Imp(All("x", R, Imp(Less(D(0), x),
                Call("HasDerivAt", Function(k), At(Function(j), x), x))), body);
        }
        for (byte j = 5; j > 0; j--)
            body = Seq(Forall, Sp, Parenthesized(Seq(Function((byte)(j - 1)), Sp, Colon, Sp, Fn(R, R))), Comma, Sp, Parenthesized(body));
        return body;
    }

}
