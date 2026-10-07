using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class FridPrefixPalindromicLengthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact palindromic length of every Frid prefix", H("The exact palindromic length of every Frid prefix"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-fridprefixpalindromiclength-claim"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/FridPrefixPalindromicLength.claim"),
                H("claim"), StatementSource.FromAuthor(Disp(Equal(F.Id("claim"),Bind(FormulaQuantifier.ForAll,"k",Naturals(),Implies(AtMost(D(1),F.Id("k")),Equal(Call("PL",Call("goldenFactor",Call("N",F.Id("k")),D(0))),Add(Multiply(D(2),F.Id("k")),D(1)))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Words/frid2018numerationpalindromes")),
                Blocks(Paragraph(Text("Conjecture 2 on printed page 12 states: “For every k ≥ 1, the prefix of the Fibonacci word of length (100)²ᵏ⁻¹101 cannot be decomposed as a concatenation of at most 2k palindromes.” N(k) is the value of that Zeckendorf numeral with weights G(0)=1,G(1)=2. goldenFactor(N(k),0) is the zero-indexed prefix of goldenWord, the fixed point of 0 -> 01 and 1 -> 0; true represents 0. PL is the minimum number of nonempty palindrome factors. The claim includes the matching upper bound, hence states the exact value 2k+1."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-fridprefixpalindromiclength-result"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/FridPrefixPalindromicLength.result"),
                H("result"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"k",Naturals(),Implies(AtMost(D(1),F.Id("k")),Equal(Call("PL",Call("goldenFactor",Call("N",F.Id("k")),D(0))),Add(Multiply(D(2),F.Id("k")),D(1))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Words/ambrozetal2019palindromiclength"), LibraryNoteRef.Create("D5/L/Words/frid2018sturmiannumeration")),
                Blocks(Paragraph(Text("Equal-width canonical encodings are partitioned into six-bit chunks. Palindrome reflection forces endpoint acceptance. The finite product potential bounds every palindrome edge by one score unit, while the explicit Frid chunk cycle has score 2k+1. Induction along any factorisation gives the lower bound, and symmetric central-word trims give the matching upper bound."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("frid-2018-fibonacci-prefix-palindromic-length"),
                    ResolutionKind.Proved)))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula domain, Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
