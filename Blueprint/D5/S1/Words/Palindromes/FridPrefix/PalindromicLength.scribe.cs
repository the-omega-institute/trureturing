using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class PalindromicLengthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimum nonempty palindrome factorisation", H("Minimum nonempty palindrome factorisation"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-palindromiclength-palfactors"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/PalindromicLength.PalFactors"),
                H("PalFactors"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"A",F.Id("Type"),Bind(FormulaQuantifier.ForAll,"w",Call("List",F.Id("A")),Bind(FormulaQuantifier.ForAll,"k",Naturals(),Equal(Call("PalFactors",F.Id("w"),F.Id("k")),Bind(FormulaQuantifier.Exists,"ps",Call("List",Call("List",F.Id("A"))),And(Equal(Call("flatten",F.Id("ps")),F.Id("w")),And(Equal(Call("length",F.Id("ps")),F.Id("k")),Bind(FormulaQuantifier.ForAll,"p",Call("List",F.Id("A")),Implies(Call("mem",F.Id("p"),F.Id("ps")),And(NotEqual(F.Id("p"),F.Id("nil")),Call("Palindrome",F.Id("p")))))))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Words/frid2018numerationpalindromes")),
                Blocks(Paragraph(Text("On printed page 9 Frid writes: “The palindromic length of a finite word u is the minimal number Q of palindromes P₁, . . . , P_Q such that u = P₁ · · · P_Q.” PalFactors(w,k) expresses the displayed concatenation using exactly k nonempty palindrome factors. Deleting empty factors preserves concatenation and cannot increase the minimum. The empty word has a zero-factor decomposition. List.flatten preserves the order of the factors."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-palindromiclength-pl"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/PalindromicLength.PL"),
                H("PL"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"A",F.Id("Type"),Bind(FormulaQuantifier.ForAll,"w",Call("List",F.Id("A")),Equal(Call("PL",F.Id("w")),Call("min",Seq(OpenBrace,F.Id("k"),Sp,InMacro,Sp,Naturals(),Sp,Mid,Sp,Call("PalFactors",F.Id("w"),F.Id("k")),CloseBrace))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Words/frid2018numerationpalindromes")),
                Blocks(Paragraph(Text("On printed page 9 Frid writes: “The palindromic length of a finite word u is the minimal number Q of palindromes P₁, . . . , P_Q such that u = P₁ · · · P_Q.” PL is this minimum, with empty factors removed. A factorisation into singleton letters makes the set nonempty; the definition uses Nat.find on that existence proof. The minimum for the empty word is zero."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-palindromiclength-pl-one-letter-lipschitz"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/PalindromicLength.pl_one_letter_lipschitz"),
                H("pl_one_letter_lipschitz"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"A",F.Id("Type"),Bind(FormulaQuantifier.ForAll,"w",Call("List",F.Id("A")),Bind(FormulaQuantifier.ForAll,"a",F.Id("A"),AtMost(Call("abs",Subtract(Call("int",Call("PL",Call("append",F.Id("w"),Call("singleton",F.Id("a"))))),Call("int",Call("PL",F.Id("w"))))),D(1))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All lengths in the absolute difference are cast to integers. Appending one singleton supplies one inequality. For the reverse inequality, removing the last letter of a palindrome splits its remainder into a shorter central palindrome and at most one singleton."))), DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula domain, Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => Seq(left, Sp, Neq, Sp, right);
    private static Formula AtMost(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
