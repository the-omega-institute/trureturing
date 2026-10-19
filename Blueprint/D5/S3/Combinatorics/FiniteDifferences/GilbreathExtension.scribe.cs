using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FiniteDifferences;

internal sealed class GilbreathExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/muney2026gilbreath");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact finite Gilbreath extension component question over every integer extension.",
        H("Finite Gilbreath extensions and maximal step-two runs"),
        Blocks(
            Node("gilbreath-difference", "Adjacent absolute differences", "difference",
                "The ordered zip of the input and its tail takes the absolute difference of each consecutive pair."),
            Node("gilbreath-row", "The finite difference triangle", "row",
                "Row zero is the input list and row r plus one is the absolute-difference row of row r. The source entry s_a^b corresponds to row s b at zero-based position a minus one, for valid triangle indices."),
            Node("gilbreath-isgilbreath", "The Gilbreath left edge", "isGilbreath",
                "For every natural r with zero less than r less than the input length, the head of row r is some one. The row-length induction gives length n minus r, and the source recurrence agrees with every valid list entry."),
            Node("gilbreath-admissible", "Eligible prefixes", "admissible",
                "A list has length n, is pairwise strictly increasing, starts with two and three, and is Gilbreath. List position i corresponds to source position i plus one."),
            Node("gilbreath-validextensions", "All integer extensions", "validExtensions",
                "An integer k belongs exactly when appending k gives a Gilbreath list. In particular k need not exceed the last prefix entry."),
            Node("gilbreath-maximalsteptworuns", "Literal maximal step-two runs", "maximalStepTwoRuns",
                "A pair a,b has a at most b in one parity class. Every integer of that parity between them belongs to X; a minus two and b plus two do not. On a finite one-parity set these endpoint pairs represent precisely its nonempty maximal runs. The literal-run bridge writes b as a plus twice a natural m and enumerates exactly a,a+2,...,a+2m. Endpoint membership and uniqueness of the right endpoint justify finite run counting."),
            Node("gilbreath-oneparity", "One integer parity class", "oneParity",
                "All members have the same remainder modulo two as some integer p. Neither even nor odd extensions are excluded in advance."),
            Node("gilbreath-extensiongeometry", "Finite geometry as a conclusion", "extensionGeometry",
                "Both the extension set and its set of literal run endpoints must be finite, and the extension set must lie in one parity class. The recursive extension preimage proves these properties for every eligible prefix; they are conclusions of the result."),
            Node("gilbreath-steptworuncount", "Counting literal runs", "stepTwoRunCount",
                "The natural cardinality counts endpoint pairs. Its use in the whole target is accompanied by explicit finiteness conclusions; the convention assigning zero to infinite sets does not discharge those conclusions."),
            Node("gilbreath-componentmaximum", "The exact whole question", "componentMaximum",
                "For every natural n at least five, all eligible prefixes satisfy the finite geometry and the upper bound two to the power n minus four; at least one eligible prefix has finite geometry and equality. This defines the question proved by the result below. No prime, uniqueness, cardinality-maximum or bounded-length substitute occurs."),
            Node("gilbreath-source-triangle", "The source index recurrence", "sourceTriangle",
                "Source row b and one-based column a correspond to sourceTriangle s b (a minus one). At every valid index this is the corresponding row-list entry, by induction using adjacent list entries. Values outside the finite triangle are irrelevant to the statement."),
            Node("gilbreath-parity-interval", "A parity interval", "parityInterval",
                "The integers from a through b congruent to a modulo two. Empty intervals are permitted. A finite cover by r such intervals gives at most r literal maximal runs, because each run start must be an interval start and a run start has a unique right endpoint."),
            Node("gilbreath-attaining-prefix", "The known attaining family", "attainingPrefix",
                "The parameter m is length minus four. Put U zero equal to the singleton two and append two to the power j plus one at step j. Then attainingPrefix m is U at m plus two followed by two to the power m plus three minus one. Thus lengths at least five are exactly Muney Definition 31 and Theorem 35. The length-four seed is (2,3,5,7). No separate resolution credit is attached to this known attaining family."),
            Describe.Lean(DescribeId.Create("gilbreath-whole-component-maximum"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The component maximum at every length"),
                StatementSource.FromAuthor(WholeFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every n at least five, every eligible prefix has finite single-parity unrestricted extension geometry and at most two to the power n minus four maximal step-two runs; an eligible prefix attains equality. The appended integer is unrestricted.")),
                    Paragraph(Text("The actual triangle gives K of s as the absolute-value preimage of K of its difference row. Each parity interval has at most two parity intervals in this preimage, including clipping at zero. The realizable bottom rows force the four-entry seed to be one parity interval. Induction therefore gives the upper bound for every length. This proof uses no graph representation.")),
                    Paragraph(Text("For the attributed attaining family, the difference of V at the next length is V at the preceding length shifted down by one. Its extension set lies between two m plus three and two to the power m plus four minus two m minus five. After shifting down by one every extension is at least two, so the absolute-value preimage has two separated reflected copies of its maximal runs. Starting with the single run from three through eleven at length four, the count doubles at every step.")),
                    Paragraph(Text("All auxiliary proofs belong to the live whole development or the explicit source-index bridge. The solved maximum-cardinality and uniqueness question and the prime Gilbreath conjecture are outside the theorem."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("muney-gilbreath-component-maximum"),
                    ResolutionKind.Proved))
        ), []));

    private static Formula WholeFormula()
    {
        Formula n = F.Id("n"), s = F.Id("s");
        Formula nat = new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
        Formula integers = new Formula.NamedConstant(FormulaIdentifier.Create("Int"));
        Formula lists = Call("List", integers);
        Formula count = Call("stepTwoRunCount", Call("validExtensions", s));
        Formula bound = Seq(D(2), Caret, Grp(Open, Subtract(n, D(4)), Close));
        Formula eligible = Call("admissible", n, s);
        Formula geometry = Call("extensionGeometry", s);
        Formula universal = All("s", lists, Implies(eligible,
            And(geometry, Relation(count, FormulaRelationOperator.LessThanOrEqual, bound))));
        Formula attainment = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("s"), lists,
            And(eligible, And(geometry, Relation(count, FormulaRelationOperator.Equal, bound))));
        return Disp(All("n", nat,
            Implies(Relation(D(5), FormulaRelationOperator.LessThanOrEqual, n),
                And(universal, attainment))));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Relation(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.And, Seq(Open, b, Close));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));

    private static DocumentBlock Node(string id, string title, string declaration, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
