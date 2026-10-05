using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class PalindromicLengthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/PalindromicLength.";
    private static readonly LibraryNoteRef Flp =
        LibraryNoteRef.Create("D5/L/Words/fridlabordepeltomaki2021automaticppl");
    private static readonly LibraryNoteRef Li =
        LibraryNoteRef.Create("D5/L/Words/li2020rulerperioddoubling");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Optimal suffix cuts give the exact minimum and transfer cut potentials to lower bounds.",
        H("Palindromic Length and Suffix Cuts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pd-palindromiclength-palfactors"),
                DeclarationHandle.Create(Prefix + "PalFactors"),
                H("Nonempty palindrome factorizations"),
                StatementSource.FromAuthor(FactorsFormula()),
                AssessedProvenance.FromLiterature(Flp),
                Blocks(Paragraph(Text("Printed page 1: “In particular, we are interested in the minimal number of palindromes needed for such a decomposition, which we call the palindromic length of a word.” The source example abbaba has length three, as (abba)(b)(a) or (a)(bb)(aba). Empty factors can be removed. PalFactors records an actual ordered list of k nonempty palindromes whose flattening is w."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pd-palindromiclength-pl"),
                DeclarationHandle.Create(Prefix + "PL"),
                H("The true minimum factor count"),
                StatementSource.FromAuthor(LengthFormula()),
                AssessedProvenance.FromLiterature(Flp),
                Blocks(Paragraph(Text("Printed page 1: “In particular, we are interested in the minimal number of palindromes needed for such a decomposition, which we call the palindromic length of a word.” The source minimum is the natural infimum of the feasible factor counts. Single-letter factorizations make that set nonempty for every finite word, and the empty word has minimum zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pd-palindromiclength-optimal-suffix-cut"),
                DeclarationHandle.Create(Prefix + "optimal_suffix_cut"),
                H("An optimal final suffix"),
                StatementSource.FromAuthor(CutFormula()),
                AssessedProvenance.FromRepo(Flp),
                Blocks(Paragraph(Text("An optimal factorization has a nonempty last factor. Its preceding length is the cut j. Replacing its preceding factorization by an optimal one proves the exact equality, rather than only an upper bound."))),
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
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
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
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula FactorsFormula()
    {
        var each = All("p", ListOf(V("A")), Imp(Mem(V("p"), V("ps")), And(
            Ne(V("p"), Seq(OpenBracket, CloseBracket)), Call("Palindrome", V("p")))));
        var factors = Ex("ps", ListOf(ListOf(V("A"))), And(
            Eqn(Call("flatten", V("ps")), V("w")),
            Eqn(Call("length", V("ps")), V("k")), each));
        return Disp(All("A", Ty("Type"), All("w", ListOf(V("A")), All("k", N(),
            IffF(Call("PalFactors", V("w"), V("k")), factors)))));
    }
    private static Formula LengthFormula()
    {
        var feasible = Seq(OpenBrace, V("k"), Colon, N(), Sp, Mid, Sp,
            Call("PalFactors", V("w"), V("k")), CloseBrace);
        return Disp(All("A", Ty("Type"), All("w", ListOf(V("A")),
            Eqn(Call("PL", V("w")), Call("sInf", feasible)))));
    }
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
            LeF(Call("val", V("B"), V("n")), Add(Call("val", V("B"), V("j")), D(1)))));
        var step = All("n", N(), Imp(LeF(V("n"), Call("length", V("w"))), cut));
        var conclusion = All("n", N(), Imp(LeF(V("n"), Call("length", V("w"))),
            LeF(Call("val", V("B"), V("n")), Call("PL", prefix))));
        return Disp(All("A", Ty("Type"), All("w", ListOf(V("A")), All("B", Fn(N(), N()),
            Imp(And(Eqn(Call("val", V("B"), D(0)), D(0)), step), conclusion)))));
    }
}
