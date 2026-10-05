using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class NonadjacentSignedDigitsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/NonadjacentSignedDigits.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite nonadjacent signed digit list realizes the minimum signed binary weight.", H("Minimum Weight of Nonadjacent Signed Digits"), Blocks(
        Describe.Lean(DescribeId.Create("pd-nonadjacentsigneddigits-signed-weight-nonadjacent"),
            DeclarationHandle.Create(Prefix + "signed_weight_nonadjacent"), H("Every nonadjacent signed expansion is minimal"),
            StatementSource.FromAuthor(NafFormula()), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Words/menezesvanoorschotvanstone1996sparse")),
            Blocks(Paragraph(Text("The list contains only minus one, zero, and one, in increasing binary-position order. Each adjacent pair contains a zero. Folding by z+2 acc computes its signed binary value, and filtering nonzero digits counts its weight. List induction resolves both possible nonzero low digits and proves that this count is the true minimum over all signed-power representations."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula ListOf(Formula value) => Call("List", value);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula NegF(Formula a) => Call("neg", a);


    private static Formula NafFormula()
    {
        var alphabet = All("z", Z(), Imp(Mem(V("z"), V("digits")),
            new Formula.Logic(Eqn(V("z"), NegF(D(1))), FormulaLogicOperator.Or,
                new Formula.Logic(Eqn(V("z"), D(0)), FormulaLogicOperator.Or, Eqn(V("z"), D(1))))));
        var relation = Lam("a", Z(), Lam("b", Z(),
            new Formula.Logic(Eqn(V("a"), D(0)), FormulaLogicOperator.Or, Eqn(V("b"), D(0)))));
        var gap = Call("IsChain", V("digits"), relation);
        var fold = Call("foldr", Lam("z", Z(), Lam("acc", Z(), Add(V("z"), Mul(D(2), V("acc"))))), D(0), V("digits"));
        var count = Call("length", Call("filter", Lam("z", Z(), Call("bne", V("z"), D(0))), V("digits")));
        return Disp(All("digits", ListOf(Z()), Imp(And(alphabet, gap), Eqn(Call("signedWeight", fold), count))));
    }

}
