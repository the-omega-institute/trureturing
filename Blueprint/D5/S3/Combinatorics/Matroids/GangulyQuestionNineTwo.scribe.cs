using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class GangulyQuestionNineTwoDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/ganguly2026graphicalsymplectic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same two looped multigraphs disprove both closure laws over each field in Question 9.2.",
        H("Ganguly Question 9.2 on 1-sums and bridge joins"),
        Blocks(
            Definition("representable", "Representable", "Graphical symplectic representability",
                AssessedProvenance.FromLiterature(Source),
                "For a finite multigraph G and field F, there is a row number k equal to the maximum "
                + "size of a Chow-independent admissible signed edge selection. There is a k-row "
                + "matrix over F with independent rows and columns indexed by edges paired with "
                + "their starred copies. The alternating pairing of every pair of rows is zero. "
                + "For every injective list of k edge IDs with a Boolean mark per entry, the "
                + "corresponding k-column minor has nonzero determinant exactly when the selection "
                + "is Chow independent. Each spanning component must be a tree or unicyclic "
                + "with odd star parity on its unique cycle. Connectivity ignores endpoint "
                + "orientation. A cycle is a nonempty connected 2-regular edge subset, counting "
                + "both incidences of a loop."),
            Definition("factor-one", "factorOne", "Triangle with two loops", AssessedProvenance.FromRepo(Source),
                "The five edge IDs have endpoints (0,1), (1,2), (2,0), (0,0), and (1,1), in order."),
            Definition("factor-two", "factorTwo", "One vertex with one loop", AssessedProvenance.FromRepo(Source),
                "The single edge is a loop at vertex 0."),
            Definition("one-sum-at", "oneSumAt", "Rooted 1-sum", AssessedProvenance.FromLiterature(Source),
                "The inputs have n and m + 1 vertices, respectively, with one selected vertex each. "
                + "On the right, exchange the selected vertex with the last label. Send that last "
                + "label to the chosen left vertex and place the other m labels after the n left "
                + "vertices. Append the edge IDs, transporting both endpoint maps."),
            Definition("bridge-at", "bridgeAt", "Rooted bridge join", AssessedProvenance.FromLiterature(Source),
                "Place all right vertices after the left vertices and append the right edge IDs "
                + "after the left edge IDs. Append one fresh edge from the chosen left vertex "
                + "to the chosen right vertex."),
            Definition("one-sum", "oneSum", "The 1-sum witness", AssessedProvenance.FromRepo(Source),
                "Form the rooted 1-sum of the two factors at left vertex 2 and right vertex 0. "
                + "The resulting graph is a triangle with a loop at every vertex."),
            Definition("bridge-join", "bridgeJoin", "The bridge-join witness", AssessedProvenance.FromRepo(Source),
                "Join the same roots of the disjoint factors by a fresh edge. The loop at vertex 3 "
                + "belongs to the right factor, and the fresh edge is the edge of ID 6."),
            Describe.Lean(
                DescribeId.Create("ganguly-question-nine-two-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Affirmative closure assertion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Question 9.2 (arXiv:2611.01241v2, printed p. 39) asks "
                        + "“Over fields of characteristic 2 with at least 4 elements, is representability "
                        + "of 𝒮(G) preserved under 1-sums and under joining two graphs by a bridge?”")),
                    Paragraph(Text("There exists a field F in Lean's Type universe (level zero) "
                        + "of characteristic two with an embedding of Fin 4 into F, over which at least "
                        + "one of the two closure laws holds. A closure law quantifies over all pairs "
                        + "of finite rooted multigraphs, encoded by arbitrary finite vertex and edge "
                        + "cardinalities, and both root choices. If both input graphs are representable "
                        + "over F, the corresponding join must be representable over F."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ganguly-question-nine-two-witnesses"),
                DeclarationHandle.Create(Module + ".question_nine_two"),
                H("Counterexamples over each qualifying field"),
                StatementSource.FromAuthor(Disp(WitnessStatement())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For any universe level u and any field F in Type u of "
                        + "characteristic two with an embedding of Fin 4 into F, both factors "
                        + "are representable and each of their two joins is nonrepresentable.")),
                    Paragraph(Text("The rank-three matrix uses a parameter distinct from zero and "
                        + "one. Its basis minors depend affinely on that parameter. Finite determinant "
                        + "checks at zero and one recover the full signed basis condition by scalar "
                        + "transport and interpolation. The rank-one matrix has unstarred column "
                        + "zero and starred column one.")),
                    Paragraph(Text("The three starred loops in the 1-sum form a basis. Finite "
                        + "signed-basis checks force each marked triangle edge into its endpoint "
                        + "plane with both coefficients nonzero. The even-star tests force the "
                        + "three gain ratios to coincide and square to one. In characteristic two "
                        + "the common ratio equals one, contradicting a one-star test.")),
                    Paragraph(Text("Checking every signed selection establishes that adjoining "
                        + "the unstarred bridge preserves Chow independence under contraction. "
                        + "Its column is nonzero by the lifted loop basis. Quotienting by its span "
                        + "transfers the signed-basis conditions to the same triangle obstruction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ganguly-question-nine-two-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Refutation of both closure laws"),
                StatementSource.FromAuthor(FormulaDsl.Disp(new Formula.Not(FormulaDsl.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Apply the asserted closure law to the two representable "
                    + "factors at the specified roots. The field-uniform witness contradicts "
                    + "representability of the selected output in either case."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string name, string title,
        AssessedProvenance provenance, string prose) => Describe.Lean(
        DescribeId.Create("ganguly-question-nine-two-" + id), DeclarationHandle.Create(Module + "." + name),
        H(title), StatementSource.WithoutFormula(), provenance, Blocks(Paragraph(Text(prose))),
        DescribeRole.Definition);

    private static Formula WitnessStatement()
    {
        var field = FormulaDsl.Id("F");
        Formula Representable(string graph) => new Formula.Apply(FormulaDsl.Id("Representable"), [field, FormulaDsl.Id(graph)]);
        Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
        Formula Implies(Formula hypothesis, Formula conclusion) =>
            new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);
        var size = new Formula.Apply(FormulaDsl.Id("Nonempty"),
            [new Formula.Apply(FormulaDsl.Id("Embedding"), [new Formula.Apply(FormulaDsl.Id("Fin"), [D(4)]), field])]);
        var fieldUniverse = Seq(Mathrm, Grp(FormulaDsl.Id("Type")), Thin, FormulaDsl.Id("u"));
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("F"), fieldUniverse,
            Implies(new Formula.Apply(FormulaDsl.Id("Field"), [field]),
                Implies(new Formula.Apply(FormulaDsl.Id("CharP"), [field, D(2)]),
                    Implies(size, And(And(Representable("factorOne"), Representable("factorTwo")),
                        And(new Formula.Not(Representable("oneSum")),
                            new Formula.Not(Representable("bridgeJoin"))))))));
    }
}
