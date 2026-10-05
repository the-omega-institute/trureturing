using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class PalindromicLengthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/PalindromicLength.";
    private static readonly LibraryNoteRef Flp =
        LibraryNoteRef.Create("D5/L/Words/fridlabordepeltomaki2021automaticppl");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Optimal suffix cuts give the exact minimum and transfer cut potentials to lower bounds.",
        H("Palindromic Length and Suffix Cuts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pd-palindromiclength-optimal-suffix-cut"),
                DeclarationHandle.Create(Prefix + "optimal_suffix_cut"),
                H("An optimal final suffix"),
                StatementSource.FromAuthor(CutFormula()),
                AssessedProvenance.FromRepo(Flp),
                Blocks(Paragraph(Text("PL and PalFactors are the canonical declarations from FridPrefix/PalindromicLength. An optimal factorization has a nonempty last factor. Its preceding length is the cut j. Replacing its preceding factorization by an optimal one proves the exact equality, rather than only an upper bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pd-palindromiclength-suffix-cut-lower-bound"),
                DeclarationHandle.Create(Prefix + "suffix_cut_lower_bound"),
                H("Potentials bound the true minimum"),
                StatementSource.FromAuthor(LowerFormula()),
                AssessedProvenance.FromRepo(Flp),
                Blocks(Paragraph(Text("A natural-valued potential starting at zero and decreasing by at most one on every palindromic suffix cut bounds the true minimum. Strong induction uses an optimal last suffix at each nonempty prefix."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula ListOf(Formula value) => Call("List", value);
    private static Formula Fn(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);

    private static Formula CutFormula()
    {
        var cut = Ex("j", N(), And(LtF(V("j"), Call("length", V("w"))),
            Call("Palindrome", Call("drop", V("j"), V("w"))),
            Eqn(Call("PL", V("w")), Add(Call("PL", Call("take", V("j"), V("w"))), D(1)))));
        return Disp(All("A", Ty("Type"), All("w", ListOf(V("A")),
            Imp(Ne(V("w"), Seq(OpenBracket, CloseBracket)), cut))));
    }
    private static Formula LowerFormula()
    {
        var prefix = Call("take", V("n"), V("w"));
        var cut = All("j", N(), Imp(And(LtF(V("j"), V("n")),
            Call("Palindrome", Call("drop", V("j"), prefix))),
            LeF(new Formula.Apply(V("B"), [V("n")]), Add(new Formula.Apply(V("B"), [V("j")]), D(1)))));
        var step = All("n", N(), Imp(LeF(V("n"), Call("length", V("w"))), cut));
        var conclusion = All("n", N(), Imp(LeF(V("n"), Call("length", V("w"))),
            LeF(new Formula.Apply(V("B"), [V("n")]), Call("PL", prefix))));
        return Disp(All("A", Ty("Type"), All("w", ListOf(V("A")), All("B", Fn(N(), N()),
            Imp(And(Eqn(new Formula.Apply(V("B"), [D(0)]), D(0)), step), conclusion)))));
    }
}
