using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes;

internal sealed class ThueMorseSignedCutDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/ThueMorseSignedCut.";
    private static readonly LibraryNoteRef Akmp = LibraryNoteRef.Create("D5/L/Words/ambrozetal2019palindromiclength");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A signed potential lower bound for mixed factorizations of literal Thue-Morse prefixes.",
        H("Signed Potential for Mixed Thue-Morse Factorizations"),
        Blocks(
            Describe.Lean(DescribeId.Create("tm-mixed-allowed"), DeclarationHandle.Create(Prefix + "Allowed"),
                H("Allowed factors"), StatementSource.FromAuthor(AllowedFormula()),
                AssessedProvenance.FromLiterature(Akmp),
                Blocks(Paragraph(Text("Section 6, pallen_classP.tex lines 624–635, defines exchange-reversal antipalindromes and the minimum number of factors that may be either kind. False encodes a and true encodes b. Exchange is Bool.not, and no change of the word or its index origin is made."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tm-transition-pd"), DeclarationHandle.Create(Prefix + "transition_period_doubling"),
                H("Adjacent transitions and period doubling"), StatementSource.FromAuthor(TransitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The adjacent transition is one exactly when neighboring letters differ. Its even and odd recursion identifies it with the complement of the literal period-doubling word. The finite substitution approximant theorem supplies that word's valuation parity. This relationship transfers both reversal symmetries to an ordinary palindrome on adjacent transitions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tm-allowed-signed-cut"), DeclarationHandle.Create(Prefix + "allowed_factor_signed_cut"),
                H("One allowed factor increases potential by at most one"), StatementSource.FromAuthor(CutFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here factor(length,start) is the original list of letters t(start+r), with 0 ≤ r < length; j−i uses natural subtraction and i<j excludes the empty factor. Even cuts use the period-doubling palindrome bound. Odd endpoints require extending the Thue-Morse factor by one letter on both sides and combining the two rounded endpoint bounds. An odd length has an even length derivative palindrome, hence length one or three. The three-letter case excludes starts zero and one modulo four. All signedWeight arguments are integer casts of natural endpoints."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tm-mixed-factors"), DeclarationHandle.Create(Prefix + "MixedFactors"),
                H("Actual consecutive mixed factorizations"), StatementSource.FromAuthor(MixedFormula()),
                AssessedProvenance.FromLiterature(Akmp),
                Blocks(Paragraph(Text("Section 6 asks for the smallest number of factors, each either a palindrome or an antipalindrome. The list of nonempty factors is flattened in its original order and must equal the entire word. This includes a zero-factor decomposition of the empty word."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tm-combined-length"), DeclarationHandle.Create(Prefix + "combinedLength"),
                H("Minimum mixed cost"), StatementSource.FromAuthor(CostFormula()),
                AssessedProvenance.FromLiterature(Akmp),
                Blocks(Paragraph(Text("Section 6, lines 631–635, considers this combined pal-antipal length. Singleton letters give a factorization of every finite word, so the natural minimum exists. The definition uses Nat.find on that existence statement."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tm-prefix-mixed-lower"), DeclarationHandle.Create(Prefix + "combined_prefix_signed_lower"),
                H("The prefix cost sandwich"), StatementSource.FromAuthor(LowerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Split an actual factorization at each successive factor. The cut bound telescopes from signedWeight(0)=0, giving the lower inequality for every factorization and hence its minimum. Every ordinary palindrome factorization is allowed, giving the upper inequality with the existing generic PL. This bound alone does not establish the Section 6 assertion of unbounded prefixes with equal costs: an unbounded attaining family and an ordinary palindromic upper bound on that family are still needed."))), DescribeRole.Theorem))));

    private static Formula V(string x) => F.Id(x);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula B() => V("Bool");
    private static Formula L() => Call("List", B());
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(V(name), [.. args]);
    private static Formula All(string x, Formula t, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), t, body);
    private static Formula Exists(string x, Formula t, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), t, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula S(Formula n) => Call("signedWeight", Call("int", n));
    private static Formula AllowedFormula() => Disp(All("w", L(), Eqn(Call("Allowed", V("w")),
        Or(Call("Palindrome", V("w")), Eqn(V("w"), Call("map", V("not"), Call("reverse", V("w"))))))));
    private static Formula TransitionFormula() => Disp(All("n", N(), Eqn(Call("transition", V("n")),
        Call("ite", new Formula.Apply(new Formula.Subscript(V("u"), Seq(Mathrm, Grp(V("pd")))), [V("n")]), D(0), D(1)))));
    private static Formula CutFormula() => Disp(All("i", N(), All("j", N(), Imp(LtF(V("i"), V("j")),
        Imp(Call("Allowed", Call("factor", Call("natSub", V("j"), V("i")), V("i"))),
            Le(S(V("j")), Add(S(V("i")), D(1))))))));
    private static Formula MixedFormula() => Disp(All("w", L(), All("k", N(), Eqn(Call("MixedFactors", V("w"), V("k")),
        Exists("ps", Call("List", L()), And(Eqn(Call("flatten", V("ps")), V("w")),
            And(Eqn(Call("length", V("ps")), V("k")), All("p", L(), Imp(Call("mem", V("p"), V("ps")),
                And(Seq(V("p"), Sp, Neq, Sp, V("nil")), Call("Allowed", V("p"))))))))))));
    private static Formula CostFormula() => Disp(All("w", L(), Eqn(Call("combinedLength", V("w")),
        Call("min", Seq(OpenBrace, V("k"), Sp, InMacro, Sp, N(), Sp, Mid, Sp,
            Call("MixedFactors", V("w"), V("k")), CloseBrace)))));
    private static Formula LowerFormula() => Disp(All("n", N(), And(
        Le(S(V("n")), Call("combinedLength", Call("factor", V("n"), D(0)))),
        Le(Call("combinedLength", Call("factor", V("n"), D(0))), Call("PL", Call("factor", V("n"), D(0)))))));
}
