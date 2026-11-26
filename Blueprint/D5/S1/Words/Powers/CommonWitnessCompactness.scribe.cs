using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Powers;

internal sealed class CommonWitnessCompactnessDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/aiswaryamanuel2026commonwitness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A globally oriented common witness exists exactly when every subrelation of at most three rows has one.",
        H("Common Witness Compactness for Finite Word Relations"),
        Blocks(Describe.Lean(
            DescribeId.Create("common-witness-iff-finite"),
            DeclarationHandle.Create(
                "D5/S1/Words/Powers/CommonWitnessCompactness.commonWitness_iff_finite"),
            H("Finite character with one global witness orientation"),
            StatementSource.FromAuthor(ClassificationFormula()),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text(
                    "For every universe level u, every alphabet A in Type u, and every set G of "
                    + "literal List A pairs, CommonWitness(G) holds exactly when every finite "
                    + "subset T of G has CommonWitness(T). CommonWitness(G) is the disjunction "
                    + "of one word z satisfying a ++ z = z ++ b for every (a,b) in G, or one "
                    + "word z satisfying z ++ a = b ++ z for every pair in G. The orientation "
                    + "is global for G; each finite T retains its own disjunction.")),
                Paragraph(Text(
                    "The statement includes empty and infinite relations, empty words, the "
                    + "neutral pair ([],[]), empty alphabets, infinite alphabets, and arbitrary "
                    + "universe levels. It assumes no Finite, Fintype, DecidableEq or Nonempty "
                    + "structure on A and does not bound witness length. It is a literal List and "
                    + "Set result, with no infinite-word or group-element endpoint.")),
                Paragraph(Text(
                    "For the inner orientation, a nonempty first component is selected from G. "
                    + "For a witness z of a ++ z = z ++ b, the word a ++ z has period length(a) "
                    + "and starts with a. Reducing indices modulo this positive period shows "
                    + "that the shorter of two such words is a prefix of the longer; cancelling "
                    + "a gives prefix comparability of the witnesses. Two distinct shared witnesses transport a "
                    + "third row through the cyclic centralizer: residuals commute with the "
                    + "anchor right word, and the cyclic centralizer classification transfers "
                    + "commutation to the row under test. If a row has at most one shared anchor "
                    + "witness, a finite three-row union forces all such unique candidates to "
                    + "agree. Rows with empty first component are neutral by length cancellation. "
                    + "The outer case follows after swapping each pair. For the global disjunction, either every finite subset admits an inner witness, or a finite inner obstruction exists. In the latter case adjoining that obstruction to any finite subset forces an outer witness, so outer finite character applies.")),
                Paragraph(Text(
                    "Aiswarya, Manuel and Sunny, arXiv:2307.06777v4, Definition 5, p. 14, and "
                    + "Lemma 6, p. 25, give the finite-alphabet common-witness principle. The cited "
                    + "source is a literature boundary: its finite-alphabet scope is recorded, "
                    + "while the arbitrary-alphabet List statement, the global orientation "
                    + "disjunction and all degenerate cases are proved here."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("common-witness-iff-three"),
            DeclarationHandle.Create(
                "D5/S1/Words/Powers/CommonWitnessCompactness.commonWitness_iff_three"),
            H("Three rows determine a common signed word"),
            StatementSource.FromAuthor(ThreeFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every universe u, alphabet A in Type u and relation G of List A pairs, "
                    + "CommonWitness(G) holds if and only if CommonWitness(T) holds for every "
                    + "finite subset T of G with ncard(T) at most three. Each T chooses its own "
                    + "word and orientation. The conclusion chooses one finite word and one "
                    + "orientation for all of G. There is no length bound, and G and A may be "
                    + "empty, finite or infinite.")),
                Paragraph(Text(
                    "Represent an inner word x by a left tag and an outer nonempty word y by a "
                    + "right tag. The empty outer word has the same equations as the empty inner "
                    + "word, so it receives the latter representation. Fix a row (a,b) with "
                    + "a nonempty. Two distinct common inner words for this row and another row "
                    + "transport every anchor inner word by the cyclic-centralizer argument. "
                    + "If x is inner and y is outer, x ++ y ++ x is inner. Cancelling the two "
                    + "copies of x recovers the outer equation, so two inner words transport "
                    + "every signed anchor word. Swapping the row components proves the same "
                    + "assertion for two outer words. For mixed signs the inner words x and "
                    + "x ++ y ++ x are distinct, since equality would force the nonempty y to "
                    + "have length zero. Thus two distinct shared signed words always transport "
                    + "every signed anchor word.")),
                Paragraph(Text(
                    "The signed words shared by the anchor and any row form a nonempty set, "
                    + "by the two-row hypothesis. If this set contains two distinct elements, "
                    + "it contains every anchor word. If all rows have this property, any "
                    + "anchor word works globally. Otherwise choose a row whose shared set "
                    + "is a singleton. Every triple containing the anchor, this row and an "
                    + "arbitrary third row forces that same singleton word, which therefore "
                    + "works globally. Repeated rows are allowed: inserting three rows gives "
                    + "a finite set of cardinality at most three. If no first component is "
                    + "nonempty, singleton solvability and length cancellation force every "
                    + "second component to be empty; the empty inner word then works.")),
                Paragraph(Text(
                    "The three-row bound is the result stated here. Definition 5, Proposition 13 "
                    + "and Lemma 6 of the cited paper supply the common-witness terminology and "
                    + "related rigidity and finite-character structure; the three-row bound "
                    + "is not attributed to that source. No claim of literature novelty or "
                    + "sharpness of the bound is made."))),
            DescribeRole.Theorem))));

    private static Formula ThreeFormula()
    {
        var alphabet = F.Id("A");
        var words = Call("List", alphabet);
        var relation = Call("Set", Call("Prod", words, words));
        var G = F.Id("G");
        var T = F.Id("T");
        var bounded = new Formula.Relation(Call("ncard", T),
            FormulaRelationOperator.LessThanOrEqual, D(3));
        var local = All("T", relation,
            Logic(Call("subset", T, G), FormulaLogicOperator.Implies,
                Logic(Call("Finite", T), FormulaLogicOperator.Implies,
                    Logic(bounded, FormulaLogicOperator.Implies, Call("CommonWitness", T)))));
        return Disp(All("u", F.Id("Universe"),
            All("A", Call("Type", F.Id("u")),
                All("G", relation, Logic(Call("CommonWitness", G), FormulaLogicOperator.Iff, local)))));
    }

    private static Formula ClassificationFormula()
    {
        var alphabet = F.Id("A");
        var words = Call("List", alphabet);
        var pair = Call("Prod", words, words);
        var relation = Call("Set", pair);
        var G = F.Id("G");
        var T = F.Id("T");
        var common = Call("CommonWitness", G);
        var finite = All("T", relation,
            Logic(Call("subset", T, G), FormulaLogicOperator.Implies,
                Logic(Call("Finite", T), FormulaLogicOperator.Implies,
                    Call("CommonWitness", T))));
        return Disp(All("u", F.Id("Universe"),
            All("A", Call("Type", F.Id("u")),
                All("G", relation, Logic(common, FormulaLogicOperator.Iff, finite)))));
    }

    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Logic(Formula left, FormulaLogicOperator operation, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), operation, Seq(Open, right, Close));
}
