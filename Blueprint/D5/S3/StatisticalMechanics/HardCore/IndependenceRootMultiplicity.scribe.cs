using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class IndependenceRootMultiplicityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.";
    private static readonly LibraryNoteRef Question =
        LibraryNoteRef.Create("D5/L/Zeros/bhardwajetal2026negativeonemultiplicity");
    private static readonly LibraryNoteRef Gutman =
        LibraryNoteRef.Create("D5/L/Zeros/levitmandrescu2013fsymmetries");

    private static readonly Formula T = F.Id("t");
    private static readonly Formula K = F.Id("k");
    private static readonly Formula X = F.Id("X");
    private static readonly Formula Nat = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula Ints = Seq(Mathbb, Grp(F.Id("Z")));
    private static readonly Formula Rats = Seq(Mathbb, Grp(F.Id("Q")));
    private static readonly Formula Claim = F.Id("Conjecture58");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A triangle with three leaves per center refutes the multiplicity bound.",
        H("Multiplicity at negative one in a clique corona"),
        Blocks(
            Describe.Lean(DescribeId.Create("corona-vertex"), DeclarationHandle.Create(Prefix + "Vertex"),
                H("Tagged centers and leaves"),
                StatementSource.FromAuthor(Disp(Parameters(Equal(Call("Vertex", T, K),
                    Call("Sum", Call("Fin", T), Call("Prod", Call("Fin", T), Call("Fin", K))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A left tag marks a center. The two coordinates of a right tag "
                    + "give the owner and the leaf index at that owner."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("corona-graph"), DeclarationHandle.Create(Prefix + "corona"),
                H("Clique corona with independent leaf fibers"),
                StatementSource.FromAuthor(Disp(Parameters(Seq(Call("corona", T, K), Sp, Colon, Sp,
                    Call("SimpleGraph", Call("Vertex", T, K)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two centers are adjacent exactly when their indices differ. A center "
                    + "and a leaf are adjacent exactly when the center is the leaf's owner, in either order. "
                    + "There are no edges between leaves. Symmetry and looplessness follow from these four cases.")),
                    new DocumentBlock.DisplayFormula(AdjacencyFormula())),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("corona-decidable-adjacency"),
                DeclarationHandle.Create(Prefix + "coronaDecidableAdj"), H("Decidable adjacency"),
                StatementSource.FromAuthor(Disp(Parameters(Call("DecidableRel", Call("Adj", Call("corona", T, K)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four tag pairs reduce adjacency to inequation, equality, equality, "
                    + "or false. Finite-index equality supplies the decisions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("corona-connected"), DeclarationHandle.Create(Prefix + "corona_connected"),
                H("Connectivity through the centers"),
                StatementSource.FromAuthor(Disp(Parameters(ImpliesIf(Positive(T),
                    Call("Connected", Call("corona", T, K)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positive t gives a center with index zero. Every other center is "
                    + "adjacent to it, and every leaf is adjacent to its own center. The condition t > 0 "
                    + "ensures a nonempty graph. No positivity assumption on k is needed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("corona-factorization"),
                DeclarationHandle.Create(Prefix + "corona_factorization"), H("The actual independence polynomial"),
                StatementSource.FromAuthor(Disp(Parameters(ImpliesIf(Positive(T), Equal(CoronaPolynomial(),
                    Multiply(Power(OnePlusX(), Exponent()),
                        Parenthesized(Add(Power(OnePlusX(), K), Multiply(Parenthesized(Seq(T, Sp, Colon, Sp, Call("Polynomial", Ints))), X))))))))),
                AssessedProvenance.FromLiterature(Gutman),
                Blocks(Paragraph(Text("The cast (t : Polynomial ℤ) is the constant polynomial given by the "
                    + "natural-number cast of t into ℤ[X]. The polynomial is the frozen independencePolynomial "
                    + "on the full vertex set. Each independent set contributes one monomial with degree its "
                    + "cardinality. The unique empty configuration contributes the constant coefficient one.")),
                    Paragraph(Text("With no center chosen, all tk leaves are available. With a center chosen, "
                    + "its own leaves and all other centers are excluded. The remaining (t−1)k leaves are free. "
                    + "The proof uses the frozen partition deletion identity to split these actual configurations. "
                    + "The factorization is Gutman's corona formula specialized to the clique and the edgeless "
                    + "graph on k vertices, as stated by Levit and Mandrescu, Theorem 1.2."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("corona-multiplicity"),
                DeclarationHandle.Create(Prefix + "corona_rootMultiplicity"), H("Exact multiplicity"),
                StatementSource.FromAuthor(Disp(Parameters(ImpliesIf(Positive(T),
                    ImpliesIf(Positive(K), Equal(Multiplicity(CoronaPolynomial()), Exponent())))))),
                AssessedProvenance.FromRepo(Gutman),
                Blocks(Paragraph(Text("The exponent (t−1)k is exact because the residual evaluates to −t at −1. "
                    + "Positive k makes (1+X)^k vanish there. For k = 0 the residual instead evaluates to 1−t."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bhardwaj-question-58"),
                DeclarationHandle.Create(Prefix + "Conjecture58"), H("Question 5.8"),
                StatementSource.FromAuthor(Disp(ClaimFormula())), AssessedProvenance.FromLiterature(Question),
                Blocks(Paragraph(Text("On page 16, Bhardwaj et al. ask whether a connected graph G on n ≥ 2 "
                    + "vertices must have mult₋₁ P_G ≤ ⌈n/2⌉ − 1. Page 1 specifies finite simple graphs and "
                    + "includes the empty independent set. The claim quantifies over a type V with a Fintype "
                    + "instance and every SimpleGraph G on V. Classical decidability imposes no additional "
                    + "graph hypothesis. Fintype.card V is the order, the division is in ℚ, and the ceiling, "
                    + "subtraction and comparison are in ℤ."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bhardwaj-question-58-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A connected twelve-vertex counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Claim))),
                AssessedProvenance.FromRepo(Question, Gutman),
                Blocks(Paragraph(Text("Take t = k = 3. The graph is a triangle with three private leaves "
                    + "at each center. It has 3 + 3·3 = 12 vertices and is connected. Its polynomial is "
                    + "(1+X)^6((1+X)^3+3X), so the residual at −1 is −3 and the multiplicity is 6. "
                    + "The proposed bound is ⌈12/2⌉ − 1 = 5. The contradiction refutes Question 5.8."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bhardwaj-et-al-2026-question-5-8"), ResolutionKind.Refuted)))));

    private static Formula Call(string name, params Formula[] parameters) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. parameters]);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Parameters(Formula body) => All("t", Nat, All("k", Nat, body));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Equal(Formula lhs, Formula rhs) => new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula LeqTo(Formula lhs, Formula rhs) => new Formula.Relation(lhs, FormulaRelationOperator.LessThanOrEqual, rhs);
    private static Formula Positive(Formula value) => new Formula.Relation(D(0), FormulaRelationOperator.LessThan, value);
    private static Formula ImpliesIf(Formula condition, Formula body) =>
        new Formula.Logic(condition, FormulaLogicOperator.Implies, body);

    private static Formula Add(Formula lhs, Formula rhs) => new Formula.Binary(lhs, FormulaBinaryOperator.Add, rhs);
    private static Formula Subtract(Formula lhs, Formula rhs) => new Formula.Binary(lhs, FormulaBinaryOperator.Subtract, rhs);
    private static Formula Multiply(Formula lhs, Formula rhs) => new Formula.Binary(lhs, FormulaBinaryOperator.Multiply, rhs);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula OnePlusX() => Parenthesized(Add(D(1), X));
    private static Formula Exponent() => Multiply(Parenthesized(Subtract(T, D(1))), K);
    private static Formula PolynomialOf(Formula graph) => Call("independencePolynomial", graph, F.Id("univ"));
    private static Formula CoronaPolynomial() => PolynomialOf(Call("corona", T, K));
    private static Formula Multiplicity(Formula polynomial) => Call("rootMultiplicity", Seq(Minus, D(1)), polynomial);

    private static Formula AdjacencyFormula()
    {
        var i = F.Id("i");
        var j = F.Id("j");
        var a = F.Id("a");
        var b = F.Id("b");
        Formula Center(Formula owner) => Call("inl", owner);
        Formula Leaf(Formula owner, Formula index) => Call("inr", Parenthesized(Seq(owner, Comma, Sp, index)));
        Formula Adjacent(Formula left, Formula right) => Call("Adj", Call("corona", T, K), left, right);
        Formula IffTo(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Iff, right);
        Formula Owners(Formula body) => All("i", Call("Fin", T), All("j", Call("Fin", T), body));
        return Parameters(new Formula.Aligned([
            Owners(IffTo(Adjacent(Center(i), Center(j)), new Formula.Relation(i, FormulaRelationOperator.NotEqual, j))),
            Owners(All("b", Call("Fin", K), IffTo(Adjacent(Center(i), Leaf(j, b)), Equal(i, j)))),
            Owners(All("a", Call("Fin", K), IffTo(Adjacent(Leaf(i, a), Center(j)), Equal(j, i)))),
            Owners(All("a", Call("Fin", K), All("b", Call("Fin", K),
                IffTo(Adjacent(Leaf(i, a), Leaf(j, b)), F.Id("False"))))),
        ]));
    }

    private static Formula ClaimFormula()
    {
        var vertices = F.Id("V");
        var graph = F.Id("G");
        var order = Call("card", vertices);
        var ceiling = Call("ceil", new Formula.Fraction(Seq(order, Sp, Colon, Sp, Rats), D(2)));
        var inequality = LeqTo(Parenthesized(Seq(Multiplicity(PolynomialOf(graph)), Sp, Colon, Sp, Ints)),
            Subtract(ceiling, D(1)));
        var proposition = All("V", F.Id("Type"), Seq(OpenBracket, Call("Fintype", vertices), CloseBracket, Comma, Sp,
            All("G", Call("SimpleGraph", vertices),
                ImpliesIf(LeqTo(D(2), order), ImpliesIf(Call("Connected", graph), inequality)))));
        return new Formula.Logic(Claim, FormulaLogicOperator.Iff, Parenthesized(proposition));
    }
}
