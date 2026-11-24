using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class FernauRystsovShortestResetPrefixDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/fernau2026shortest");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-by-four DFA product whose shortest reset has a different initial letter from the shortest first-factor reset.",
        H("A shortest first-factor reset can miss the product optimum"),
        Blocks(Describe.Lean(
            DescribeId.Create("shortest-reset-prefix-result"),
            DeclarationHandle.Create("D5/S0/Automata/FernauRystsovShortestResetPrefix.result"),
            H("The shortest-first strategy can be suboptimal"),
            StatementSource.FromAuthor(Refutation()),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text("Take a shared alphabet Fin(k) and state sets Fin(m) and Fin(n), with all three sizes positive. "
                    + "Each DFA has a total transition for each state and letter. The product A × B applies the same letter in both coordinates. "
                    + "The predicate R(A,S,w) means that the image I(A,S,w) of S under the word w is a singleton. "
                    + "Write Q(A) for the full state set and use juxtaposition for word concatenation. "
                    + "All word quantifiers include the empty word. The start and accepting fields have no role in the reset predicates.")),
                Paragraph(Text("The fourth question of §7 asks about choosing a shortest first-factor reset before solving subset synchronization on the second factor. "
                    + "Here optimality means attaining the global product minimum. Lemma 6 already gives feasibility by concatenating whole-factor resets. "
                    + "Once u resets A, a suffix v resets the residual second-factor subset exactly when uv resets the product. "
                    + "For a globally shortest uv, any shorter reset of that subset would give a shorter product reset. "
                    + "This is why the shortest-prefix formulation implies the suffix minimality in the displayed proposition.")),
                Paragraph(Text("On the alphabet {a,b}, the first factor has transitions a ↦ (0,0,1) and b ↦ (1,2,0). "
                    + "The second has a ↦ (1,1,2,0) and b ↦ (0,2,3,0), with states listed in increasing order. "
                    + "Evaluating every word of lengths zero through four gives the unique shortest first- and second-factor resets aa and bbb "
                    + "and the unique shortest product reset bbaa. The product reset begins with b, so aa cannot be its prefix. "
                    + "After aa the second-factor image is {1,2}, whose shortest reset is bbb. "
                    + "The staged word aabbb thus has length five, while bbaa has length four."))),
            DescribeRole.Theorem))));

    private static Formula Refutation()
    {
        Formula k = F.Id("k"), m = F.Id("m"), n = F.Id("n");
        Formula a = F.Id("A"), b = F.Id("B");
        Formula r = F.Id("r"), s = F.Id("s"), u = F.Id("u"), v = F.Id("v"), w = F.Id("w");
        var naturals = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        var alphabet = Call("Fin", k);
        var words = F.Seq(alphabet, F.Caret, F.Grp(F.Star));
        var product = Parenthesized(F.Seq(a, F.Sp, F.Times, F.Sp, b));
        var fullA = Call("Q", a);
        var fullB = Call("Q", b);
        var residual = Call("I", b, fullB, u);
        var fullProduct = Call("Q", product);
        var joined = F.Seq(u, v);
        var premises = And(Parenthesized(Bind(F.Exists, r, words, Call("R", a, fullA, r))),
            Parenthesized(Bind(F.Exists, s, words, Call("R", b, fullB, s))));
        var conclusion = new Formula.Aligned([
            Bind(F.Exists, F.Seq(u, F.Comma, v), words, F.Open),
            Shortest(a, fullA, u, w, words),
            F.Seq(F.Land, F.Sp, Shortest(b, residual, v, w, words)),
            F.Seq(F.Land, F.Sp, Shortest(product, fullProduct, joined, w, words), F.Close),
        ]);

        return F.Disp(F.Seq(F.Neg, F.Sp, Parenthesized(new Formula.Aligned([
            Bind(F.Forall, F.Seq(k, F.Comma, m, F.Comma, n), naturals,
                F.Seq(And(Positive(k), And(Positive(m), Positive(n))), F.Sp, F.To)),
            Bind(F.Forall, a, Call("DFA", alphabet, Call("Fin", m)),
                F.Seq(F.Forall, F.Sp, b, F.Colon, F.Sp, Call("DFA", alphabet, Call("Fin", n)), F.Comma)),
            F.Seq(premises, F.Sp, F.To),
            conclusion,
        ]))));
    }

    private static Formula Shortest(Formula automaton, Formula states, Formula word,
        Formula competitor, Formula words) =>
        Parenthesized(And(Call("R", automaton, states, word),
            Parenthesized(Bind(F.Forall, competitor, words,
                new Formula.Logic(Call("R", automaton, states, competitor), FormulaLogicOperator.Implies,
                    new Formula.Relation(Length(word), FormulaRelationOperator.LessThanOrEqual,
                        Length(competitor)))))));

    private static Formula Call(string function, params Formula[] args) =>
        new Formula.Apply(F.Seq(F.Operatorname, F.Grp(F.Id(function))), [.. args]);

    private static Formula Bind(Formula quantifier, Formula variable, Formula type, Formula body) =>
        F.Seq(quantifier, F.Sp, variable, F.Colon, F.Sp, type, F.Comma, F.Sp, body);

    private static Formula Positive(Formula size) =>
        new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, size);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Length(Formula word) => F.Seq(F.Lvert, F.Sp, word, F.Rvert);

    private static Formula Parenthesized(Formula value) => F.Seq(F.Open, value, F.Close);
}
