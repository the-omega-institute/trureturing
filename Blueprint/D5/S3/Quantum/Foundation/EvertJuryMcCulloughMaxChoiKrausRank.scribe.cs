using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class EvertJuryMcCulloughMaxChoiKrausRankDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/evertjurymccullough2026completely");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The maximum Choi–Kraus rank is n³ for each of the left-unit and common-unit classes.",
        H("Maximum Choi–Kraus rank of matrix products with units"), Blocks(
            Definition("CMatrix", "Square complex matrices", MatrixFormula(),
                "The natural number n gives the common size of the row and column index sets."),
            Definition("MatrixProduct", "Complex bilinear matrix products", ProductFormula(),
                "Both inputs are n by n and the output is m by m. Each arrow in the displayed type is complex-linear."),
            Definition("block", "An input block", BlockFormula(),
                "The block indices come first and the matrix indices come second."),
            Definition("jointAmplification", "Joint block amplification", AmplificationFormula(),
                "The two input blocks are evaluated independently. The output indices are ordered as a pair of block indices followed by a coordinate in the output matrix."),
            Definition("IsJointlyCompletelyPositive", "Joint complete positivity", JcpFormula(),
                "Equation (2.1) requires positivity on two positive semidefinite block matrices at every positive block size."),
            Definition("HasKrausRepresentation", "Kraus representations of length N", KrausFormula(),
                "Theorem 2.1 uses n² by m coefficients and the conjugate transpose on the left. The length zero gives an empty sum."),
            Definition("choiKrausRank", "Minimum Kraus length", RankFormula(),
                "Remark 2.2 defines the rank by the minimum length. The infimum is taken in the extended natural numbers, so an empty set of admissible lengths has value infinity."),
            Definition("choiMatrix", "Choi matrix in input-input-output order", ChoiFormula(),
                "The explicit tensor sum in Theorem 2.1 uses E(i,j) and E(s,t) as n by n matrix units. Swapping both input positions in the nested block convention preserves rank and positivity."),
            Definition("IsLeftUnit", "Left unit", UnitFormula(true),
                "Section 5.3 requires the left identity at every complex matrix Y. L ranges over all complex matrices."),
            Definition("IsRightUnit", "Right unit", UnitFormula(false),
                "Section 5.3 requires the right identity at every complex matrix X."),
            Definition("IsUnit", "Common two-sided unit", CommonUnitFormula(),
                "The same complex matrix T supplies both identities."),
            Definition("claim", "The two clauses of Question 1",
                IffOf(X("claim"), ClaimBody()),
                "Question 1 in Section 5.3, printed page 22, asks “What is the maximum Choi-Kraus rank of a jcp product with a left unit?” and “What is the maximum Choi-Kraus rank of a jcp product with a unit?” For every n ≥ 1, Lean considers complex bilinear products with both inputs and the output of size n and requires joint complete positivity at every positive block size on every pair of positive semidefinite block inputs. The first class requires a left unit, and the second requires one matrix satisfying both unit identities. The units range over all complex n by n matrices. For each class, the extended-natural infimum of Kraus lengths is at most n³ for every qualifying product and equals n³ for some qualifying product.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("ejm-max-choi-kraus-rank-result"), DeclarationHandle.Create(Owner + ".result"),
                H("The two sharp maxima"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("Test joint block positivity at size n on two copies of the matrix-unit block matrix given by the unnormalized maximally entangled dyad. The result is the Choi matrix. Simultaneously permute row and column indices to use the output-first Choi convention for a linear map. Its action on simple Kronecker tensors is the original bilinear map, by their values on matrix units and bilinearity.")),
                    Paragraph(Text("The positive semidefinite Choi matrix gives a rectangular Kraus family indexed by the n³ Choi coordinates. Conversely, each Kraus coefficient acts by a sandwich on a permutation of the tensor product of the two block inputs, yielding positivity at every block size. Flattening the coefficients expresses the Choi matrix as a sum of N outer products, so its rank is at most N. If the Choi matrix is positive definite, this forces every admissible length to be at least n³.")),
                    Paragraph(Text("For n at least two let J be the all-ones matrix and I the identity. The weighted Schur product with weights I + J has common unit T = J − I/2. With H = (2n − 1)I − J, add the product of the two functionals A ↦ Tr(HA) and B ↦ Tr(HB), times I. The functional vanishes at T, and H is positive definite. The added Choi matrix is the tensor product of the two transposes of H and I. It is positive definite, and the weighted Schur contribution is positive semidefinite.")),
                    Paragraph(Text("At n = 1 ordinary scalar multiplication has unit 1 and positive-definite Choi matrix. In every dimension the common-unit example also attains the left-unit maximum. The upper bound applies to all jointly completely positive square products, independently of their units. For n at least two the attaining unit is indefinite."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("evert-jury-mccullough-2026-max-choi-kraus-rank"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(
        string name, string title, Formula formula, string prose, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("ejm-" + name.ToLowerInvariant()), DeclarationHandle.Create(Owner + "." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula MatrixFormula() => All("n", Nat,
        Equal(Call("CMatrix", X("n")), Matrix(Fin("n"), Fin("n"))));

    private static Formula ProductFormula() => Sizes(
        Equal(Call("MatrixProduct", X("n"), X("m")),
            LinearArrow(Square("n"), LinearArrow(Square("n"), Square("m")))));

    private static Formula BlockFormula()
    {
        Formula blockEntry = At(Call("block", X("A"), X("i"), X("j")), X("a"), X("b"));
        Formula sourceEntry = Call("A", Pair(X("i"), X("a")), Pair(X("j"), X("b")));
        return All("n", Nat, All("ell", Nat, All("A", BlockMatrix(),
            All("i", Fin("ell"), All("j", Fin("ell"), All("a", Fin("n"), All("b", Fin("n"),
                Equal(blockEntry, sourceEntry))))))));
    }

    private static Formula AmplificationFormula()
    {
        Formula entry = At(Call("jointAmplification", Phi, X("A"), X("B")),
            Pair(Pair(X("i"), X("s")), X("a")), Pair(Pair(X("j"), X("t")), X("b")));
        Formula value = At(At(Phi, Call("block", X("A"), X("i"), X("j")),
            Call("block", X("B"), X("s"), X("t"))), X("a"), X("b"));
        return Products(SizesForBlocks(Entries("ell", Equal(entry, value))));
    }

    private static Formula JcpFormula()
    {
        Formula condition = SizesForBlocks(Imply(Pos(X("A")), Imply(Pos(X("B")),
            Pos(Call("jointAmplification", Phi, X("A"), X("B"))))), positiveSize: true);
        return Products(IffOf(Jcp(Phi), condition));
    }

    private static Formula KrausFormula()
    {
        Formula coefficient = Call("V", X("k"));
        Formula term = Seq(new Formula.Power(coefficient, Star), Sp,
            Call("kronecker", X("A"), X("B")), Sp, coefficient);
        Formula sum = Seq(Sum, Underscore, Grp(X("k"), Sp, InMacro, Sp, Fin("N")), Sp, term);
        Formula identity = All("A", Square("n"), All("B", Square("n"), Equal(At(Phi, X("A"), X("B")), sum)));
        Formula family = new Formula.TypeArrow(Fin("N"), Matrix(PairType(Fin("n"), Fin("n")), Fin("m")));
        return Products(All("N", Nat, IffOf(HasKraus(Phi, X("N")), Some("V", family, identity))));
    }

    private static Formula RankFormula()
    {
        Formula feasible = Some("N", Nat, And(Equal(X("r"), Typed(X("N"), ENat)), HasKraus(Phi, X("N"))));
        Formula lengths = Seq(OpenBrace, Typed(X("r"), ENat), Sp, Mid, Sp, feasible, CloseBrace);
        return Products(Equal(Rank(Phi), Call("sInf", lengths)));
    }

    private static Formula ChoiFormula()
    {
        Formula entry = At(Call("choiMatrix", Phi), Pair(Pair(X("i"), X("s")), X("a")),
            Pair(Pair(X("j"), X("t")), X("b")));
        Formula value = At(At(Phi, Subscript(X("E"), Pair(X("i"), X("j"))),
            Subscript(X("E"), Pair(X("s"), X("t")))), X("a"), X("b"));
        return Products(Entries("n", Equal(entry, value)));
    }

    private static Formula UnitFormula(bool left)
    {
        string unit = left ? "L" : "R";
        string variable = left ? "Y" : "X";
        Formula value = left ? At(Phi, X(unit), X(variable)) : At(Phi, X(variable), X(unit));
        return All("n", Nat, All("Phi", Product("n", "n"), All(unit, Square("n"),
            IffOf(Unit(left ? "IsLeftUnit" : "IsRightUnit", unit),
                All(variable, Square("n"), Equal(value, X(variable)))))));
    }

    private static Formula CommonUnitFormula() => All("n", Nat, All("Phi", Product("n", "n"),
        All("T", Square("n"), IffOf(Unit("IsUnit", "T"),
            And(Unit("IsLeftUnit", "T"), Unit("IsRightUnit", "T"))))));

    private static Formula ClaimBody() => All("n", Nat, Imply(AtLeastOne(X("n")),
        And(Maximum("IsLeftUnit", "L"), Maximum("IsUnit", "T"))));

    private static Formula Maximum(string predicate, string unit)
    {
        Formula unitExists = Some(unit, Square("n"), Unit(predicate, unit));
        Formula cube = Typed(new Formula.Power(X("n"), D(3)), ENat);
        Formula bound = All("Phi", Product("n", "n"), Imply(Jcp(Phi),
            Imply(unitExists, new Formula.Relation(Rank(Phi), FormulaRelationOperator.LessThanOrEqual, cube))));
        Formula attainment = Some("Phi", Product("n", "n"), And(Jcp(Phi),
            And(unitExists, Equal(Rank(Phi), cube))));
        return And(bound, attainment);
    }

    private static Formula Sizes(Formula body) => All("n", Nat, All("m", Nat, body));
    private static Formula Products(Formula body) => Sizes(All("Phi", Product("n", "m"), body));
    private static Formula SizesForBlocks(Formula body, bool positiveSize = false)
    {
        Formula inputs = All("A", BlockMatrix(), All("B", BlockMatrix(), body));
        return All("ell", Nat, positiveSize ? Imply(AtLeastOne(X("ell")), inputs) : inputs);
    }

    private static Formula Entries(string size, Formula body) =>
        All("i", Fin(size), All("j", Fin(size), All("s", Fin(size), All("t", Fin(size),
            All("a", Fin("m"), All("b", Fin("m"), body))))));

    private static readonly Formula Nat = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula ENat = Seq(Nat, Underscore, Grp(Infty));
    private static readonly Formula Complex = Seq(Mathbb, Grp(F.Id("C")));

    private static Formula X(string name) => name == "Phi" ? Phi : F.Id(name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => At(X(name), args);
    private static Formula Parenthesize(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesize(Seq(value, Colon, Sp, type));
    private static Formula Pair(Formula a, Formula b) => Parenthesize(Seq(a, Comma, Sp, b));
    private static Formula PairType(Formula a, Formula b) => Parenthesize(Seq(a, Sp, Times, Sp, b));
    private static Formula Fin(string size) => Call("Fin", X(size));
    private static Formula Square(string size) => Call("CMatrix", X(size));
    private static Formula Matrix(Formula rows, Formula columns) => Call("Matrix", rows, columns, Complex);
    private static Formula BlockMatrix() => Matrix(PairType(Fin("ell"), Fin("n")), PairType(Fin("ell"), Fin("n")));
    private static Formula Product(string n, string m) => Call("MatrixProduct", X(n), X(m));
    private static Formula Pos(Formula matrix) => Call("PosSemidef", matrix);
    private static Formula Jcp(Formula product) => Call("IsJointlyCompletelyPositive", product);
    private static Formula HasKraus(Formula product, Formula count) => Call("HasKrausRepresentation", product, count);
    private static Formula Rank(Formula product) => Call("choiKrausRank", product);
    private static Formula Unit(string predicate, string value) => Call(predicate, Phi, X(value));

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesize(body));

    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesize(body));

    private static Formula LinearArrow(Formula a, Formula b) =>
        Seq(a, Sp, Rightarrow, Underscore, Grp(Complex), Sp, b);

    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula AtLeastOne(Formula n) => new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n);
    private static Formula Subscript(Formula a, Formula b) => new Formula.Subscript(a, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesize(a), Sp, Land, Sp, Parenthesize(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(a, Sp, Iff, Sp, Parenthesize(b));
    private static Formula Imply(Formula a, Formula b) => Seq(Parenthesize(a), Sp, Implies, Sp, Parenthesize(b));
}
