using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ClusterMutation;

internal sealed class HuangMaBinaryDeltaInvariantDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/ClusterMutation/HuangMaBinaryDeltaInvariant";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Eigenstructure/huangma2026mutation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed positive skew-symmetrizer permits at most two delta residues.",
        H("The binary delta invariant for a fixed skew-symmetrizer"),
        Blocks(
            Node("symmetrizer", "A positive skew-symmetrizer", "IsSkewSymmetrizer",
                SymmetrizerFormula(), AssessedProvenance.FromLiterature(Source),
                "Section 1, p. 1: “A matrix B = (b_ij) ∈ M_n(Z) is called skew-symmetrizable if there exists a diagonal matrix D = diag(d_1, …, d_n) with positive integers d_i such that DB is skew-symmetric. Such a matrix D is called a skew-symmetrizer of B.” The index set is Fin n, the entries of B are integers, and d is a vector of positive natural numbers. The entrywise equation is exactly skew-symmetry of diag(d)·B; it also forces every diagonal entry of B to vanish.",
                DescribeRole.Definition),
            Node("symmetrization", "The real symmetrization", "symmetrization",
                SymmetrizationFormula(), AssessedProvenance.FromLiterature(Source),
                "Section 1, p. 2: “we define its symmetrization to be the symmetric matrix S(B) = (s_ij) ∈ M_n(R) given by s_ij = 2 if i = j, s_ij = sgn(b_ij)√|b_ij b_ji| if i < j, s_ij = sgn(b_ji)√|b_ij b_ji| if i > j, where sgn(x) denotes the sign of x, with the convention sgn(0) = 0.” The displayed ite expressions follow these three cases in order. Integer entries and Int.sign are coerced to Real, Real.sqrt is the nonnegative square root, and the absolute value is taken after multiplying the real entries.",
                DescribeRole.Definition),
            Node("claim", "Huang–Ma Remark 2.7", "claim",
                Disp(IffFormula(F.Id("claim"), ClaimBody())), AssessedProvenance.FromLiterature(Source),
                "Remark 2.7, p. 7: “We also conjecture that for any fixed n and any choice of skew-symmetrizer d₁, …, dₙ, the invariant δ is binary. This is supported by several explicit computations.” Definition 1.3, p. 2: “The δ-invariant of a skew-symmetrizable matrix B ∈ M_n(Z) is defined as δ(B) := det(S(B)) (mod 4)”. Binary means at most two residues, which may coincide; n = 1 has only the residue 2. The two residues are chosen after n and d and before B. The integer k records both integrality of the real determinant and its residue in ZMod 4. The formula also includes n = 0, whose determinant is 1.",
                DescribeRole.Definition),
            Node("result", "The delta invariant has at most two values", "result",
                Disp(ClaimBody()), AssessedProvenance.FromRepo(Source),
                "The real symmetrization is diagonally similar to the integer matrix with diagonal 2, upper entries B(i,j), and lower entries −B(i,j). In odd size its determinant is even. In size 2m, pairing each determinant term with the inverse permutation gives the congruence det(A) = (−1)^m det(B) in ZMod 4. When det(DB) = 0, it is already a square. When det(DB) ≠ 0, the rational alternating form associated to DB is nondegenerate and has a symplectic basis. This basis gives a Gram matrix of determinant one, and change of basis shows that det(DB) is a rational square. Thus the product of the weights times det(B) is an integer square. Cancelling a common nonzero weight in two square products shows that any two nonzero attainable determinant residues agree in ZMod 4. The sign twist therefore leaves at most one nonzero residue, in addition to zero. This proves the conjecture without a coprimality assumption on the weights; it does not assert that both residues are attained or identify the even-size nonzero residue explicitly.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("huang-ma-2026-binary-delta-invariant"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("huang-ma-binary-delta-" + id),
            DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Imp(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula IffFormula(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula NatType() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula IntType() => new Formula.Integers();
    private static Formula RealType() => new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula FinType(Formula n) => Call("Fin", n);
    private static Formula Weights(Formula n) => Seq(FinType(n), Sp, To, Sp, NatType());
    private static Formula MatrixType(Formula n) => Call("Matrix", FinType(n), FinType(n), IntType());
    private static Formula ResidueType() => Call("ZMod", D(4));
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Positive(Formula n, Formula d) =>
        All("i", FinType(n), Less(D(0), Apply(d, F.Id("i"))));

    private static Formula SymmetrizerFormula()
    {
        var n = F.Id("n"); var d = F.Id("d"); var b = F.Id("B");
        var i = F.Id("i"); var j = F.Id("j");
        var equation = Equal(Times(Cast(Apply(d, i), IntType()), Apply(b, i, j)),
            new Formula.Negate(Parenthesized(Times(Cast(Apply(d, j), IntType()), Apply(b, j, i)))));
        return Disp(All("n", NatType(), All("d", Weights(n), All("B", MatrixType(n),
            IffFormula(Call("IsSkewSymmetrizer", d, b), And(Positive(n, d),
                All("i", FinType(n), All("j", FinType(n), equation))))))));
    }

    private static Formula SymmetrizationFormula()
    {
        var n = F.Id("n"); var b = F.Id("B"); var i = F.Id("i"); var j = F.Id("j");
        var entry = Apply(b, i, j); var reverse = Apply(b, j, i);
        var magnitude = Apply(Qualified("Real", "sqrt"),
            new Formula.Absolute(Times(Cast(Cast(entry, IntType()), RealType()), Cast(reverse, RealType()))));
        var upper = Times(Cast(Apply(Qualified("Int", "sign"), entry), RealType()), magnitude);
        var lower = Times(Cast(Apply(Qualified("Int", "sign"), reverse), RealType()), magnitude);
        return Disp(All("n", NatType(), All("B", MatrixType(n), All("i", FinType(n),
            All("j", FinType(n), Equal(Apply(Call("symmetrization", b), i, j),
                Call("ite", Equal(i, j), D(2), Call("ite", Less(i, j), upper, lower))))))));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n"); var d = F.Id("d"); var b = F.Id("B"); var k = F.Id("k");
        var residue = Cast(k, ResidueType());
        var conclusion = Ex("k", IntType(), And(
            Equal(Apply(Qualified("Matrix", "det"), Call("symmetrization", b)), Cast(k, RealType())),
            Or(Equal(residue, F.Id("r1")), Equal(residue, F.Id("r2")))));
        return All("n", NatType(), All("d", Weights(n), Imp(Positive(n, d),
            Ex("r1", ResidueType(), Ex("r2", ResidueType(), All("B", MatrixType(n),
                Imp(Call("IsSkewSymmetrizer", d, b), conclusion)))))));
    }
}
