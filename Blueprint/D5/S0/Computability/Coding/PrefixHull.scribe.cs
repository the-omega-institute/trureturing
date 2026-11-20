using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Coding;

internal sealed class PrefixHullDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite labelled word family has a finite prefix basis for its least right-unitary submonoid, with exact coefficients and no increase in label count.",
        H("Finite prefix bases for least right-unitary word monoids"),
        Blocks(
            Paragraph(Text(
                "Let alpha be a type in an arbitrary universe, n a natural number, and "
                    + "f : Fin n -> List alpha a labelled family of finite words. A containing "
                    + "right-unitary monoid is a set M of words containing the empty word and "
                    + "every f(i), closed under concatenation, and satisfying: if x belongs "
                    + "to M and x ++ y belongs to M, then y belongs to M. The least hull H "
                    + "is the literal intersection of every such M. Right unitarity requires "
                    + "membership of the left factor; it is not closure under arbitrary suffixes.")),
            Paragraph(Text(
                "IsPrefix(x,y) means that x ++ r = y for some word r, including the empty "
                    + "residual. For g : Fin m -> List alpha and a coefficient word s over "
                    + "Fin m, flatMap(g,s) concatenates the g-labelled words in order. The "
                    + "empty coefficient word evaluates to the empty word.")),
            Describe.Lean(
                DescribeId.Create("finite-prefix-basis-least-right-unitary-hull"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/PrefixHull.finite_prefix_basis_least_right_unitary_hull"),
                H("Exact bounded prefix basis of the least hull"),
                StatementSource.FromAuthor(HullFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Construct the generators by induction on the label count and strong "
                            + "induction on total word length. Besides nonemptiness, prefix "
                            + "separation and exact coefficients, retain the invariant that "
                            + "every returned generator belongs to every admissible containing "
                            + "monoid of the current family. Deleting an empty label preserves "
                            + "this invariant because every admissible monoid contains the empty word.")),
                    Paragraph(Text(
                        "If the nonempty labelled family is prefix-separated, return it with "
                            + "singleton coefficients. Otherwise choose distinct labels i,j "
                            + "with f(i) ++ r = f(j) and replace the word at j by r. Since "
                            + "f(i) is nonempty, total length strictly decreases. Every "
                            + "admissible containing monoid contains r by right unitarity. "
                            + "The reverse containment condition follows by concatenation, so "
                            + "the local replacement preserves admissible containing monoids. "
                            + "Transport coefficients by the substitution taking j to [i,j] "
                            + "and every other label k to [k], then compose using flatMap.")),
                    Paragraph(Text(
                        "For the terminal generators g, let L be all flatMap(g,s). It contains "
                            + "the empty word and every input, and is closed under concatenation. "
                            + "To prove right unitarity, suppose flatMap(g,s) ++ y = flatMap(g,t) "
                            + "for an arbitrary word y. Induct on s. When s is nonempty, t "
                            + "cannot be empty because all generators are nonempty. The first "
                            + "generators on the two sides are comparable prefixes of the same "
                            + "word, so prefix separation identifies their labels. Cancel that "
                            + "common generator and apply the induction. Thus y also belongs to L.")),
                    Paragraph(Text(
                        "Since L is an admissible containing monoid, intersection membership "
                            + "implies membership in L. Conversely, the retained invariant puts "
                            + "each generator in every admissible containing monoid, and closure "
                            + "under concatenation puts every word of L in each such monoid. "
                            + "This proves equality with the literal least hull, together with "
                            + "the exact factorization of every original labelled input.")),
                    Paragraph(Text(
                        "No finiteness, inhabitedness or decidable equality assumption on "
                            + "alpha is needed. Empty alphabets, n = 0, m = 0, empty input "
                            + "words and duplicate labels are included. Nonempty means that "
                            + "each generator word is nonempty; the generator family may be "
                            + "empty. The theorem asserts m <= n and does not assert minimum "
                            + "cardinality, a complexity bound or a converse characterization. "
                            + "The source provenance describes this construction in the "
                            + "repository; it makes no claim of literature novelty."))),
                DescribeRole.Theorem)),
        []));

    private static Formula HullFormula()
    {
        Formula alpha = F.Id("alpha"), n = F.Id("n"), m = F.Id("m");
        Formula i = F.Id("i"), j = F.Id("j"), w = F.Id("w");
        Formula x = F.Id("x"), y = F.Id("y"), monoid = F.Id("M");
        Formula word = Call("List", alpha);
        Formula nil = Seq(OpenBracket, CloseBracket);
        Formula concat = Call("append", x, y);
        Formula closed = All("x", word, All("y", word,
            Imp(Member(x, monoid), Imp(Member(y, monoid), Member(concat, monoid)))));
        Formula unitary = All("x", word, All("y", word,
            Imp(Member(x, monoid), Imp(Member(concat, monoid), Member(y, monoid)))));
        Formula contains = All("i", Call("Fin", n), Member(Call("f", i), monoid));
        Formula hull = All("M", Call("Set", word), Imp(Member(nil, monoid),
            Imp(closed, Imp(unitary, Imp(contains, Member(w, monoid))))));
        Formula nonempty = All("i", Call("Fin", m),
            Seq(Call("g", i), Sp, Neq, Sp, nil));
        Formula separated = All("i", Call("Fin", m), All("j", Call("Fin", m),
            Imp(Call("IsPrefix", Call("g", i), Call("g", j)), Equal(i, j))));
        Formula exact = All("i", Call("Fin", n),
            Equal(Call("f", i), Call("flatMap", F.Id("g"), Call("c", i))));
        Formula generated = Some("s", Call("List", Call("Fin", m)),
            Equal(w, Call("flatMap", F.Id("g"), F.Id("s"))));
        Formula least = All("w", word, new Formula.Logic(hull, FormulaLogicOperator.Iff, generated));
        Formula conclusion = Some("m", NatType(), And(Le(m, n),
            Some("g", Arrow(Call("Fin", m), word),
                Some("c", Arrow(Call("Fin", n), Call("List", Call("Fin", m))),
                    And(nonempty, And(separated, And(exact, least)))))));
        return Disp(All("alpha", Seq(Type(), Caret, Grp(Star)),
            All("n", NatType(), All("f", Arrow(Call("Fin", n), word), conclusion))));
    }

    private static Formula NatType() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Type() => new Formula.NamedConstant(FormulaIdentifier.Create("Type"));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Arrow(Formula a, Formula b) => Seq(Open, a, Sp, To, Sp, b, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
