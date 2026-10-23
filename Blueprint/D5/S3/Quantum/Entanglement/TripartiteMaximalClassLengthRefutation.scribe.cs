using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class TripartiteMaximalClassLengthRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/buniy2024maximallyentangledclasses");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A tripartite state of dimensions (3, 3, 7) has coordinate length nine and all four kernel dimensions zero, contradicting the proposed lower bound eleven.",
        H("The tripartite maximal-class length bound fails"), Blocks(
            Paragraph(Text(
                "A tripartite state is a complex coefficient array in a fixed product basis. "
                    + "The contractions below are complex linear maps formed by multiplying coefficients without complex conjugation. "
                    + "Their kernel dimensions are the four algebraic entanglement invariants of Appendix A. "
                    + "The length counts nonzero coefficients in this basis; it depends on the basis. "
                    + "All dimensions and lengths are natural numbers, and subtraction is natural-number subtraction, truncated at zero.")),
            Node("State", "Tripartite coefficient arrays", StateFormula(),
                "The coordinates in the product basis are indexed by Fin d1, Fin d2 and Fin d3, with complex coefficients.",
                AssessedProvenance.FromLiterature(Source)),
            Node("flat1", "Contraction over the first factor", Flat1Formula(),
                "Equation (A1) contracts the first index against a vector in the first factor. Its kernel is the space K1.",
                AssessedProvenance.FromLiterature(Source)),
            Node("flat2", "Contraction over the second factor", Flat2Formula(),
                "Equation (A2) contracts the second index against a vector in the second factor. Its kernel is the space K2.",
                AssessedProvenance.FromLiterature(Source)),
            Node("flat3", "Contraction over the third factor", Flat3Formula(),
                "Equation (A3) contracts the third index against a vector in the third factor. Its kernel is the space K3. The contracted vector coordinate is indexed by k, the summation index.",
                AssessedProvenance.FromLiterature(Source)),
            Node("block1", "The first family of array contractions", Block1Formula(),
                "Equation (A4) sums over the second and third indices, leaving two indices in the first factor.",
                AssessedProvenance.FromLiterature(Source)),
            Node("block2", "The second family of array contractions", Block2Formula(),
                "Equation (A5) sums over the first and third indices, leaving two indices in the second factor.",
                AssessedProvenance.FromLiterature(Source)),
            Node("block3", "The third family of array contractions", Block3Formula(),
                "Equation (A6) sums over the first and second indices, leaving two indices in the third factor.",
                AssessedProvenance.FromLiterature(Source)),
            Node("joint", "The three contraction families together", JointFormula(),
                "LinearMap.prod combines the three families, with the second and third grouped together. Its kernel consists of arrays satisfying all three families of equations and is the space K123 of Appendix A.",
                AssessedProvenance.FromLiterature(Source)),
            Node("n1", "The first kernel dimension", InvariantFormula("n1", "flat1"),
                "The invariant n1 is the complex dimension of K1 in Appendix A.",
                AssessedProvenance.FromLiterature(Source)),
            Node("n2", "The second kernel dimension", InvariantFormula("n2", "flat2"),
                "The invariant n2 is the complex dimension of K2 in Appendix A.",
                AssessedProvenance.FromLiterature(Source)),
            Node("n3", "The third kernel dimension", InvariantFormula("n3", "flat3"),
                "The invariant n3 is the complex dimension of K3 in Appendix A.",
                AssessedProvenance.FromLiterature(Source)),
            Node("n123", "The joint kernel dimension", InvariantFormula("n123", "joint"),
                "The invariant n123 is the complex dimension of K123 in Appendix A. This is the intersection of the kernels of the three array contractions.",
                AssessedProvenance.FromLiterature(Source)),
            Node("InMEC", "The maximally entangled class", InMecFormula(),
                "Definition II.1 requires each of the four invariants to attain its least value among all states of the same dimensions, simultaneously.",
                AssessedProvenance.FromLiterature(Source)),
            Node("coordSupport", "The nonzero coordinates", SupportFormula(),
                "The support selects exactly the product-basis indices whose coefficients are nonzero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("length", "Coordinate length", LengthFormula(),
                "The length in Section III and equation (2) is the cardinality of the coordinate support.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The proposed tripartite length lower bound", ClaimFormula(),
                "The clause of Conjecture III.4 with all three dimensions at least three asserts that the shortest length in the maximally entangled class is d1 + d2 + d3 - 2. Its lower-bound assertion requires every state in that class to have at least this length.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("tripartite-mec-length-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A length-nine state in dimensions three, three and seven"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "At dimensions (3, 3, 7), take the state whose seven slices are the six off-diagonal 3 by 3 matrix units and the identity. "
                            + "In zero-based coordinates its coefficients are one at "
                            + "(0,1,0), (0,2,1), (1,0,2), (1,2,3), (2,0,4), (2,1,5), "
                            + "(0,0,6), (1,1,6) and (2,2,6), and zero elsewhere. Its length is nine.")),
                    Paragraph(Text(
                        "The identity slice makes the first two flattenings injective, and the seven linearly independent slices make the third injective. "
                            + "For an array in the joint kernel, the third contraction family forces every slice to be diagonal with trace zero. "
                            + "The first two families force two diagonal entries of each of slices zero through five to vanish, and the trace equations force the third. "
                            + "The diagonal equations of the first family then force all diagonal entries of slice six to vanish. "
                            + "Thus the joint kernel also contains only zero.")),
                    Paragraph(Text(
                        "All four invariants are zero, their least possible value, so this state belongs to the maximally entangled class. "
                            + "Its length nine is less than 3 + 3 + 7 - 2 = 11, refuting the stated lower bound."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("buniy-feger-kephart-2024-tripartite-mec-length-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("tripartite-mec-length-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula StateFormula() => Dimensions(Equal(State(), Functions(CoordinateIndex())));

    private static Formula Flat1Formula() => StateBinder(All("w", Functions(FinOf("d1")),
        All("j", FinOf("d2"), All("k", FinOf("d3"), Equal(
            At(Typed(LocalCall("flat1", V("v")),
                LinearArrow(Functions(FinOf("d1")), Functions(Product(FinOf("d2"), FinOf("d3"))))),
                V("w"), Pair(V("j"), V("k"))),
            SumOver("i", FinOf("d1"), Multiply(
                At(V("v"), Triple(V("i"), V("j"), V("k"))), At(V("w"), V("i")))))))));

    private static Formula Flat2Formula() => StateBinder(All("w", Functions(FinOf("d2")),
        All("i", FinOf("d1"), All("k", FinOf("d3"), Equal(
            At(Typed(LocalCall("flat2", V("v")),
                LinearArrow(Functions(FinOf("d2")), Functions(Product(FinOf("d1"), FinOf("d3"))))),
                V("w"), Pair(V("i"), V("k"))),
            SumOver("j", FinOf("d2"), Multiply(
                At(V("v"), Triple(V("i"), V("j"), V("k"))), At(V("w"), V("j")))))))));

    private static Formula Flat3Formula() => StateBinder(All("w", Functions(FinOf("d3")),
        All("i", FinOf("d1"), All("j", FinOf("d2"), Equal(
            At(Typed(LocalCall("flat3", V("v")),
                LinearArrow(Functions(FinOf("d3")), Functions(Product(FinOf("d1"), FinOf("d2"))))),
                V("w"), Pair(V("i"), V("j"))),
            SumOver("k", FinOf("d3"), Multiply(
                At(V("v"), Triple(V("i"), V("j"), V("k"))), At(V("w"), V("k")))))))));

    private static Formula Block1Formula() => StateBinder(All("z", State(),
        All("a", FinOf("d1"), All("b", FinOf("d1"), Equal(
            At(Typed(LocalCall("block1", V("v")), LinearArrow(State(), BlockSpace("d1"))),
                V("z"), Pair(V("a"), V("b"))),
            SumOver("j", FinOf("d2"), SumOver("k", FinOf("d3"), Multiply(
                At(V("v"), Triple(V("a"), V("j"), V("k"))),
                At(V("z"), Triple(V("b"), V("j"), V("k")))))))))));

    private static Formula Block2Formula() => StateBinder(All("z", State(),
        All("a", FinOf("d2"), All("b", FinOf("d2"), Equal(
            At(Typed(LocalCall("block2", V("v")), LinearArrow(State(), BlockSpace("d2"))),
                V("z"), Pair(V("a"), V("b"))),
            SumOver("i", FinOf("d1"), SumOver("k", FinOf("d3"), Multiply(
                At(V("v"), Triple(V("i"), V("a"), V("k"))),
                At(V("z"), Triple(V("i"), V("b"), V("k")))))))))));

    private static Formula Block3Formula() => StateBinder(All("z", State(),
        All("a", FinOf("d3"), All("b", FinOf("d3"), Equal(
            At(Typed(LocalCall("block3", V("v")), LinearArrow(State(), BlockSpace("d3"))),
                V("z"), Pair(V("a"), V("b"))),
            SumOver("i", FinOf("d1"), SumOver("j", FinOf("d2"), Multiply(
                At(V("v"), Triple(V("i"), V("j"), V("a"))),
                At(V("z"), Triple(V("i"), V("j"), V("b")))))))))));

    private static Formula JointFormula() => StateBinder(Equal(
        Typed(LocalCall("joint", V("v")), LinearArrow(State(),
            Product(BlockSpace("d1"), Product(BlockSpace("d2"), BlockSpace("d3"))))),
        At(Qualified("LinearMap", "prod"), LocalCall("block1", V("v")),
            At(Qualified("LinearMap", "prod"), LocalCall("block2", V("v")), LocalCall("block3", V("v"))))));

    private static Formula InvariantFormula(string invariant, string map) => StateBinder(Equal(
        Typed(LocalCall(invariant, V("v")), Naturals()),
        At(Qualified("Module", "finrank"), Complexes(),
            At(Qualified("LinearMap", "ker"), LocalCall(map, V("v"))))));

    private static Formula InMecFormula() => StateBinder(Equivalence(LocalCall("InMEC", V("v")),
        All("w", State(), And(
            LE(LocalCall("n1", V("v")), LocalCall("n1", V("w"))), And(
                LE(LocalCall("n2", V("v")), LocalCall("n2", V("w"))), And(
                    LE(LocalCall("n3", V("v")), LocalCall("n3", V("w"))),
                    LE(LocalCall("n123", V("v")), LocalCall("n123", V("w")))))))));

    private static Formula SupportFormula() => StateBinder(Equal(
        Typed(LocalCall("coordSupport", V("v")), At(Qualified("Finset"), CoordinateIndex())),
        At(Qualified("Finset", "filter"),
            LambdaOf("p", CoordinateIndex(), NotEqual(At(V("v"), V("p")), D(0))),
            Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), CoordinateIndex())))));

    private static Formula LengthFormula() => StateBinder(Equal(
        Typed(LocalCall("length", V("v")), Naturals()),
        At(Qualified("Finset", "card"), LocalCall("coordSupport", V("v")))));

    private static Formula ClaimFormula() => Equivalence(Local("claim"), Dimensions(
        Imp(LE(D(3), V("d1")), Imp(LE(D(3), V("d2")), Imp(LE(D(3), V("d3")),
            All("v", State(), Imp(LocalCall("InMEC", V("v")),
                LE(Subtract(Add(Add(V("d1"), V("d2")), V("d3")), D(2)),
                    LocalCall("length", V("v"))))))))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(V(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Entanglement",
        "TripartiteMaximalClassLengthRefutation", name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula FinOf(string dimension) => At(Qualified("Fin"), V(dimension));
    private static Formula Product(Formula left, Formula right) => Parenthesized(Seq(left, Sp, Times, Sp, right));
    private static Formula CoordinateIndex() => Product(FinOf("d1"), Product(FinOf("d2"), FinOf("d3")));
    private static Formula State() => LocalCall("State", V("d1"), V("d2"), V("d3"));
    private static Formula Functions(Formula domain) => Parenthesized(new Formula.TypeArrow(domain, Complexes()));
    private static Formula LinearArrow(Formula domain, Formula codomain) =>
        At(Qualified("LinearMap"), At(Qualified("RingHom", "id"), Complexes()), domain, codomain);
    private static Formula BlockSpace(string dimension) => Functions(Product(FinOf(dimension), FinOf(dimension)));
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Triple(Formula first, Formula second, Formula third) =>
        Parenthesized(Seq(first, Comma, Sp, second, Comma, Sp, third));
    private static Formula Dimensions(Formula body) =>
        All("d1", Naturals(), All("d2", Naturals(), All("d3", Naturals(), body)));
    private static Formula StateBinder(Formula body) => Dimensions(All("v", State(), body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(V(name), type)), Sp, Parenthesized(body));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
