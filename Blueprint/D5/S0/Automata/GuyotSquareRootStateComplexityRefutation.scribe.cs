using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class GuyotSquareRootStateComplexityRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S0/Automata/GuyotSquareRootStateComplexityRefutation";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/guyot2024state");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The square root of the subword closure of abcdabcdabdc requires at least sixteen complete DFA states.",
        H("A counterexample to Guyot's square-root state bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("square-root-language"),
                DeclarationHandle.Create(Module + ".squareRootLanguage"),
                H("Square root of a subword closure"),
                StatementSource.FromAuthor(Disp(LanguageBody())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The predicate Sublist means scattered subsequence, allowing omitted letters while "
                    + "preserving their order. Append joins two words, so the test uses two consecutive copies of x."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("guyot-square-root-bound-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Universal upper-bound conjunct of Conjecture 1"),
                StatementSource.FromAuthor(Disp(
                    new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Conjecture 1 in §2.2 states “∀ n ∈ ℕ₍>₀₎, κ(√↓(Uₙ)) = α(n) ≤ c(n)² − c(n) + 3.”")),
                    Paragraph(Text(
                        "The upper-bound conjunct concerns α(n), the largest quotient count for words of "
                        + "length at most n. The conjectured equality involving Uₙ is separate.")),
                    Paragraph(Text(
                        "For each positive n, each finite alphabet A, and each word w of length at most n, "
                        + "the bound calls for a complete DFA M on Fin(m) whose accepted language is exactly "
                        + "the square root of the subword closure of w. Nat.div gives c(n) as (n + 2) div 3. "
                        + "The expression uses natural subtraction, which agrees with ordinary subtraction "
                        + "since c(n)² is at least c(n).")),
                    Paragraph(Text(
                        "The source counts all distinct left quotients, including the empty quotient when it occurs. "
                        + "Every quotient is the continuation language of a reached DFA state. Conversely, "
                        + "the distinct quotients form a complete DFA with transitions given by further left "
                        + "quotienting, and its finite state set can be indexed by Fin(m)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("guyot-square-root-bound-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Sixteen distinct quotients at length twelve"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Use n = 12 and the alphabet Fin(4), with a, b, c, d represented by 0, 1, 2, 3. "
                        + "For w = abcdabcdabdc, the bound allows at most 15 states.")),
                    Paragraph(Text(
                        "The selected prefixes are the empty word, a, b, c, d, aa, ab, ac, ad, ba, "
                        + "bc, bd, ca, cd, da, and bcd. Among the empty suffix and the four one-letter suffixes, "
                        + "each pair of prefixes has a suffix for which the sublist test on the doubled "
                        + "concatenation gives opposite answers.")),
                    Paragraph(Text(
                        "Mathlib's leftQuotient_accepts_apply identifies the left quotient by a prefix "
                        + "with the language accepted from the state reached by that prefix. Thus the "
                        + "sixteen prefixes reach distinct states, contradicting the bound of fifteen."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("guyot-2024-square-root-state-complexity"),
                    ResolutionKind.Refuted)))));

    private static Formula LanguageBody()
    {
        var alphabet = F.Id("A");
        var word = F.Id("w");
        var x = F.Id("x");
        var sublist = Call("Sublist", Call("append", x, x), word);
        var set = Seq(OpenBrace, x, Sp, Colon, Sp, Call("List", alphabet), Sp, Mid, Sp, sublist, CloseBrace);
        return Bind(FormulaQuantifier.ForAll, "A", F.Id("Type"),
            Bind(FormulaQuantifier.ForAll, "w", Call("List", alphabet),
                Equal(Call("squareRootLanguage", word), set)));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var alphabet = F.Id("A");
        var word = F.Id("w");
        var m = F.Id("m");
        var machine = F.Id("M");
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        var c = Call("div", new Formula.Binary(n, FormulaBinaryOperator.Add, D(2)), D(3));
        var cSquared = Seq(c, Caret, Grp(D(2)));
        var bound = new Formula.Binary(
            new Formula.Binary(cSquared, FormulaBinaryOperator.Subtract, c), FormulaBinaryOperator.Add, D(3));
        var accepts = Equal(Call("accepts", machine), Call("squareRootLanguage", word));
        var dfa = Bind(FormulaQuantifier.Exists, "M", Call("DFA", alphabet, Call("Fin", m)), accepts);
        var bounded = Bind(FormulaQuantifier.Exists, "m", naturals,
            new Formula.Logic(Le(m, bound), FormulaLogicOperator.And, Parenthesized(dfa)));
        var words = Bind(FormulaQuantifier.ForAll, "w", Call("List", alphabet),
            new Formula.Logic(Le(Call("length", word), n), FormulaLogicOperator.Implies, bounded));
        var alphabets = Bind(FormulaQuantifier.ForAll, "A", F.Id("Type"),
            Seq(OpenBracket, Call("Finite", alphabet), CloseBracket, Sp, words));
        return Bind(FormulaQuantifier.ForAll, "n", naturals, new Formula.Logic(
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n),
            FormulaLogicOperator.Implies, Parenthesized(alphabets)));
    }

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), domain, body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
}
