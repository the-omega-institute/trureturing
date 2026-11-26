using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Powers;

internal sealed class CommonWitnessCompactnessDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/aiswaryamanuel2026commonwitness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A globally oriented common witness exists exactly when every finite subrelation has one.",
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
                    + "The single-equation theorem in ConjugacyNormalForm gives prefix comparability "
                    + "of any two anchor witnesses. Two distinct shared witnesses transport a "
                    + "third row through the cyclic centralizer: residuals commute with the "
                    + "anchor right word, and the cyclic centralizer classification transfers "
                    + "commutation to the row under test. If a row has at most one shared anchor "
                    + "witness, a finite three-row union forces all such unique candidates to "
                    + "agree. Rows with empty first component are neutral by length cancellation. "
                    + "The outer case follows after swapping each pair. For the global disjunction, either every finite subset admits an inner witness, or a finite inner obstruction exists. In the latter case adjoining that obstruction to any finite subset forces an outer witness, so outer finite character applies.")),
                Paragraph(Text(
                    "Aiswarya, Manuel and Sunny, arXiv:2307.06777v4, Definition 5 and Lemma 6, "
                    + "p. 25, gives the finite-alphabet common-witness principle. The cited "
                    + "source is a literature boundary: its finite-alphabet scope is recorded, "
                    + "while the arbitrary-alphabet List statement, the global orientation "
                    + "disjunction and all degenerate cases are proved here."))),
            DescribeRole.Theorem))));

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
