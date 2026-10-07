using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.HiguchiSudbery;

internal sealed class HermiteEntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A cubic touching negMulLog at one sixth and one half majorizes it on the nonnegative half-line.",
        H("HermiteEntropy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pnat"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/HiguchiSudbery/HermiteEntropy.pNat"),
                H("The cubic majorant"),
                StatementSource.FromAuthor(Disp(All("x", R, Eqn(Call("pNat", F.Id("x")), Seq(new Formula.Fraction(Seq(D(4), Minus, D(3), Cdot, Sp, Qualified("Real", "log", D(3))), D(8)), Plus, Parenthesized(new Formula.Fraction(Seq(Minus, D(1, 1), Plus, D(2), Cdot, Sp, Qualified("Real", "log", D(2)), Plus, D(1, 2), Cdot, Sp, Qualified("Real", "log", D(3))), D(2))), Cdot, Sp, F.Id("x"), Plus, Parenthesized(new Formula.Fraction(Seq(D(3, 6), Minus, D(3, 9), Cdot, Sp, Qualified("Real", "log", D(3))), D(2))), Cdot, Sp, new Formula.Power(F.Id("x"), D(2)), Plus, D(1, 8), Cdot, Sp, Parenthesized(Seq(Qualified("Real", "log", D(3)), Minus, D(1))), Cdot, Sp, new Formula.Power(F.Id("x"), D(3))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four coefficients are displayed in full. The argument and logarithms are real; the divisions are real divisions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hermite-majorant"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/HiguchiSudbery/HermiteEntropy.hermite_majorant"),
                H("Majorization including zero"),
                StatementSource.FromAuthor(Disp(All("x", R, Imp(Leq(D(0), F.Id("x")), Leq(Qualified("Real", "negMulLog", F.Id("x")), Call("pNat", F.Id("x"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The difference has two double contacts and a positive fourth derivative on the positive half-line. Continuity of negMulLog and the polynomial includes zero."))),
                DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Eqn(Formula lhs, Formula rhs) => new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula Leq(Formula lhs, Formula rhs) => new Formula.Relation(lhs, FormulaRelationOperator.LessThanOrEqual, rhs);
    private static Formula Imp(Formula lhs, Formula rhs) => new Formula.Logic(Parenthesized(lhs), FormulaLogicOperator.Implies, Parenthesized(rhs));
    private static Formula R => Call("Real");

}
