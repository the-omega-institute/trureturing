using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Hypercube;

internal sealed class HypercubeOddIndependenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Hypercube/HypercubeOddIndependence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/caro2025oddindependence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The odd independence ratio of the Boolean cube converges to one half through all even dimensions.",
        H("Odd independence in even dimensional Boolean cubes"),
        Blocks(
            Paragraph(Text(
                "The graph Q_d consists of all Boolean functions on Fin d, with adjacency at "
                    + "Hamming distance exactly one. Write E for the even parity class. The "
                    + "argument uses binary parity checks, as in the classical Hamming construction "
                    + "described in Kleitman's Matrix Hamming Codes, Sections 9.1 to 9.3. Only the "
                    + "syndrome update under a coordinate flip is needed; no perfectness property "
                    + "for an extended code is assumed.")),
            Describe.Lean(
                DescribeId.Create("odd-independent-set"),
                DeclarationHandle.Create(Prefix + "IsOddIndependent"),
                H("Odd independent sets"),
                StatementSource.FromAuthor(Disp(OddIndependentFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A finite set S is independent if none of its vertices are adjacent to one "
                        + "another. At each vertex outside S, the number of neighbours belonging "
                        + "to S must be zero or odd. Zero is explicitly permitted; a vertex "
                        + "outside S need not be dominated. Counts use the intersection of the "
                        + "actual cube neighbour set with S."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("odd-independence-number"),
                DeclarationHandle.Create(Prefix + "oddIndependenceNumber"),
                H("The finite maximum"),
                StatementSource.FromAuthor(Disp(MaximumFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The number is the greatest cardinality attained by an odd independent set, "
                        + "bounded by the full vertex count 2^d. The empty set is admissible, so "
                        + "the selected maximum is attained. Every admissible set has cardinality "
                        + "at most this maximum. Thus the invariant is an actual finite maximum, "
                        + "rather than the size of the particular construction below."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("even-cube-odd-independence-limit"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The limit through all even dimensions"),
                StatementSource.FromAuthor(Disp(LimitFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix k greater than zero and any even d at least 2^k. Label 2^k of the "
                            + "coordinates once each by the vectors in the binary k-dimensional "
                            + "space, including the zero vector. Give every remaining coordinate "
                            + "the zero label. There are an even number of remaining coordinates. "
                            + "Every nonzero label occurs once and zero occurs an odd number of "
                            + "times. Define the syndrome of a vertex to be the sum of the labels "
                            + "at its occupied coordinates. Flipping coordinate i adds its label "
                            + "to the syndrome and reverses vertex parity.")),
                    Paragraph(Text(
                        "For any syndrome a, delete its class from E and call the remaining "
                            + "set S. It is independent because parity changes on every cube edge. "
                            + "An external even vertex has zero neighbours in S. For an odd vertex "
                            + "x, all d neighbours are even. Exactly the coordinates labelled by "
                            + "syndrome(x)+a lead to the deleted class. This count is odd, so its "
                            + "complement among an even number d of coordinates is odd. Hence S "
                            + "satisfies the zero-or-odd condition at every external vertex.")),
                    Paragraph(Text(
                        "The 2^k syndrome classes partition E. The finite pigeonhole principle "
                            + "gives a class of size at most |E|/2^k. Flipping one fixed coordinate "
                            + "bijects the two parity classes, so |E|=2^d/2. Deleting a smallest "
                            + "syndrome class therefore leaves at least "
                            + "2^d times (1/2-1/(2 times 2^k)) vertices. Conversely, any independent "
                            + "set and its image under one fixed coordinate flip are disjoint and "
                            + "have equal cardinality. Its cardinality is at most 2^d/2.")),
                    Paragraph(Text(
                        "The actual maximum lies between these lower and upper bounds. Choose "
                            + "k so that 1/(2 times 2^k) is below the given positive real epsilon, "
                            + "and take D=2^k. The same construction works for every even d at least "
                            + "D. Dividing by the positive real number 2^d gives the absolute error "
                            + "bound in the theorem. This proves the final asymptotic question in "
                            + "Problem 40 and does not determine the exact maximum at each finite "
                            + "even dimension."))),
                DescribeRole.Theorem)),
        []));

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Invoke(string name, params Formula[] arguments) => App(Named(name), arguments);
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Method(Formula value, string name, params Formula[] arguments) =>
        arguments.Length == 0 ? Seq(Parenthesized(value), Dot, Named(name))
            : App(Seq(Parenthesized(value), Dot, Named(name)), arguments);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula NatType() => Named("Nat");
    private static Formula RealType() => Seq(Mathbb, Grp(X("R")));
    private static Formula VertexType(Formula n) =>
        new Formula.TypeArrow(Invoke("Fin", n), Named("Bool"));
    private static Formula SetType(Formula n) => Invoke("Finset", Parenthesized(VertexType(n)));
    private static Formula Member(Formula x, Formula s) => Rel(x, FormulaRelationOperator.MemberOf, s);
    private static Formula Card(Formula s) => Method(s, "card");

    private static Formula OddIndependentFormula()
    {
        Formula n = X("n"), s = X("S"), x = X("x"), y = X("y");
        Formula graph = Invoke("hypercube", n);
        Formula independence = All("x", VertexType(n), Imp(Member(x, s),
            All("y", VertexType(n), Imp(Member(y, s),
                new Formula.Not(Parenthesized(Method(graph, "Adj", x, y)))))));
        Formula count = Card(App(Qualified("Finset", "inter"), Method(graph, "neighborFinset", x), s));
        Formula external = All("x", VertexType(n), Imp(new Formula.Not(Parenthesized(Member(x, s))),
            Logic(Equal(count, D(0)), FormulaLogicOperator.Or, Invoke("Odd", count))));
        return All("n", NatType(), All("S", SetType(n),
            Logic(Invoke("IsOddIndependent", s), FormulaLogicOperator.Iff, And(independence, external))));
    }

    private static Formula MaximumFormula()
    {
        Formula n = X("n"), s = X("S"), m = X("m");
        Formula predicate = Parenthesized(Seq(LambdaLower, Sp, Typed(m, NatType()), Sp, Mapsto, Sp,
            Parenthesized(Some("S", SetType(n), And(Invoke("IsOddIndependent", s), Equal(Card(s), m))))));
        return All("n", NatType(), Equal(Invoke("oddIndependenceNumber", n),
            App(Qualified("Nat", "findGreatest"), predicate, new Formula.Power(D(2), n))));
    }

    private static Formula LimitFormula()
    {
        Formula epsilon = X("epsilon"), d = X("d"), threshold = X("D");
        Formula ratio = new Formula.Fraction(Typed(Invoke("oddIndependenceNumber", d), RealType()),
            Typed(new Formula.Power(D(2), d), RealType()));
        Formula error = new Formula.Absolute(Subtract(ratio, new Formula.Fraction(D(1), D(2))));
        return All("epsilon", RealType(), Imp(Rel(D(0), FormulaRelationOperator.LessThan, epsilon),
            Some("D", NatType(), All("d", NatType(), Imp(Invoke("Even", d),
                Imp(Rel(threshold, FormulaRelationOperator.LessThanOrEqual, d),
                    Rel(error, FormulaRelationOperator.LessThan, epsilon)))))));
    }
}
