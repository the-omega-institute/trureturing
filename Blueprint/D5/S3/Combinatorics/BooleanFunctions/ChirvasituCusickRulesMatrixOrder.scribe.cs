using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BooleanFunctions;

internal sealed class ChirvasituCusickRulesMatrixOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/chirvasitucusick2024quadraticrotation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A zero trace of the twenty-fourth power contradicts the proposed order at (8,4).",
        H("A trace obstruction to the rules-matrix order conjecture"),
        Blocks(
            Node("H0", "The first Hadamard block", H0Formula(),
                "Section 6, page 18, defines H0 := [[1, 1], [1, −1]]. Entries are integers.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("H1", "The second Hadamard block", H1Formula(),
                "Section 6, page 18, defines H1 := [[1, 1], [−1, 1]]. Entries are integers.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pad", "Column padding", PadFormula(),
                "Section 6, page 19: “by πₖ(M) (or πₖM) the matrix obtained by appending k all-0 columns after each column of M (‘π’ is meant to stand for ‘pad’);” Indices start at zero. Nat.div is natural-number division; Fin.mk displays the index value, with its bound proof suppressed.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rot", "Simultaneous row rotation", RotFormula(),
                "Section 6, page 19: “and by ρₖ(M) (or ρₖM) the matrix obtained by rotation all rows of M simultaneously rightward k times.” The formula uses natural subtraction and reduction modulo n; Fin.mk suppresses its bound proof.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("blockH", "The alternating Hadamard block choice", BlockHFormula(),
                "Section 6, page 19: “Specifically, the rows in (6-2) alternate in whether or not an H₁ is substituted in batches of 2ʲ⁻¹:” Block k uses H0 first, followed by H1 after each batch. Nat.div is natural-number division and j − 1 is natural subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("R", "The binomial rules matrix", RFormula(),
                "Equation (6-3), page 19, stacks the rotated padded blocks in increasing block index. The same page states: “Again, this is a 2ⁱ × 2ⁱ matrix.” The dimension 2ⁱ applies for 1 ≤ i, including the source range i > j ≥ 1. The inverse finProdFinEquiv assigns row a to block p.1 and row p.2; its forward map sends (k,c) to c + 2k. Fin.cast changes the column bound using 2^(i−1) − 1 + 1 = 2^(i−1); proof arguments are suppressed.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Rsq", "The real square rules matrix", RsqFormula(),
                "Rsq reindexes the rows of R to its column type using commutativity of natural multiplication, then maps every integer entry to the real numbers. Fin.cast suppresses the equality proof.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("claim", "Chirvasitu–Cusick Conjecture 6.1", Eqn(Call("claim"), Parenthesized(ClaimBody())),
                "Conjecture 6.1, page 19: “For i > j ≥ 1 the eigenvalues of the matrix R(i, j) of (6-3) are all √2-scaled roots of unity. Moreover, the multiplicative order of R(i,j)/√2 is precisely 2 · lcm(4, i − j, i + j).” Both conjuncts range over natural i and j with 1 ≤ j < i. The first uses the complex spectrum; the second uses orderOf in the monoid of real square matrices. The square root in the first conjunct is cast from Real to Complex.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Refutation at (8,4)", new Formula.Not(Parenthesized(ClaimBody())),
                "For i = 8 and j = 4 the asserted order is 24. The reindexed integer matrix R(8,4) has zero trace after its twenty-fourth power: a signed Pauli transport ends with the opposite sign. Order 24 would instead force that power to equal 4096 times the identity, whose trace is 1048576. This disproves the conjunction. The exact order 48, a corrected universal order formula and the universal eigenvalue assertion are not proved here.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("cc-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("chirvasitu-cusick-2024-rules-matrix-order-conjecture-6-1"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula NatType() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula IntType() => new Formula.Integers();
    private static Formula RealType() => new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula ComplexType() => new Formula.NamedConstant(FormulaIdentifier.Create("Complex"));
    private static Formula FinType(Formula n) => Call("Fin", n);
    private static Formula MatrixType(Formula r, Formula c, Formula field) => Call("Matrix", r, c, field);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        arguments.Length == 0 ? Seq(Operatorname, Grp(V(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. arguments]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Apply(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Leq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Mem(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Pow(Formula left, Formula right) => new Formula.Power(left, right);
    private static Formula Val(Formula value) => Call("val", value);
    private static Formula Proj(Formula value, byte index) => Seq(Parenthesized(value), Dot, D(index));
    private static Formula NatDiv(Formula a, Formula b) => Apply(Qualified("Nat", "div"), a, b);
    private static Formula NatMod(Formula a, Formula b) => Apply(Qualified("Nat", "mod"), a, b);
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Seq(Operatorname, Grp(V("if")), Sp, condition, Sp, Operatorname, Grp(V("then")), Sp,
            yes, Sp, Operatorname, Grp(V("else")), Sp, no);
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(Operatorname, Grp(V("fun")), Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body);
    private static Formula Matrix2(Formula a, Formula b, Formula c, Formula d) => Seq(
        Begin, Grp(V("pmatrix")), a, Amp, b, RowBreak, c, Amp, d, End, Grp(V("pmatrix")));

    private static Formula H0Formula() => Eqn(Call("H0"), Matrix2(D(1), D(1), D(1), new Formula.Negate(D(1))));
    private static Formula H1Formula() => Eqn(Call("H1"), Matrix2(D(1), D(1), new Formula.Negate(D(1)), D(1)));

    private static Formula PadFormula()
    {
        var r = V("r"); var c = V("c"); var k = V("k"); var m = V("M"); var a = V("a"); var b = V("b");
        var body = If(Eqn(NatMod(Val(b), Add(k, D(1))), D(0)),
            Apply(m, a, Apply(Qualified("Fin", "mk"), NatDiv(Val(b), Add(k, D(1))))), D(0));
        return All("r", NatType(), All("c", NatType(), All("k", NatType(),
            All("M", MatrixType(FinType(r), FinType(c), IntType()),
                Eqn(Call("pad", k, m), Parenthesized(LambdaOf("a", FinType(r),
                    LambdaOf("b", FinType(Mul(c, Add(k, D(1)))), body))))))));
    }

    private static Formula RotFormula()
    {
        var r = V("r"); var n = V("n"); var k = V("k"); var m = V("M"); var a = V("a"); var b = V("b");
        var index = NatMod(Sub(Add(Val(b), n), NatMod(k, n)), n);
        var equality = Eqn(Call("rot", k, m), Parenthesized(LambdaOf("a", FinType(r),
            LambdaOf("b", FinType(n), Apply(m, a, Apply(Qualified("Fin", "mk"), index))))));
        return All("r", NatType(), All("n", NatType(), Seq(OpenBracket, Call("NeZero", n), CloseBracket, Sp,
            All("k", NatType(), All("M", MatrixType(FinType(r), FinType(n), IntType()), equality)))));
    }

    private static Formula BlockHFormula()
    {
        var j = V("j"); var k = V("k");
        return All("j", NatType(), All("k", NatType(), Eqn(Call("blockH", j, k),
            If(Eqn(NatMod(NatDiv(k, Pow(D(2), Sub(j, D(1)))), D(2)), D(0)), Call("H0"), Call("H1")))));
    }

    private static Formula RFormula()
    {
        var i = V("i"); var j = V("j"); var a = V("a"); var b = V("b"); var p = V("p");
        var half = Pow(D(2), Sub(i, D(1)));
        var inverse = Seq(Operatorname, Grp(V("finProdFinEquiv")), Dot, Operatorname, Grp(V("symm")));
        var value = Apply(Call("rot", Val(Proj(p, 1)), Call("pad", Sub(half, D(1)),
            Call("blockH", j, Val(Proj(p, 1))))), Proj(p, 2), Apply(Qualified("Fin", "cast"), b));
        var body = Seq(Operatorname, Grp(V("let")), Sp, p, Eq, Apply(inverse, a), Semi, Sp, value);
        return All("i", NatType(), All("j", NatType(), Eqn(Call("R", i, j),
            Parenthesized(LambdaOf("a", FinType(Mul(half, D(2))),
                LambdaOf("b", FinType(Mul(D(2), half)), body))))));
    }

    private static Formula RsqFormula()
    {
        var i = V("i"); var j = V("j");
        var cast = Seq(Parenthesized(Qualified("Int", "cast")), Colon, Sp, IntType(), Sp, To, Sp, RealType());
        return All("i", NatType(), All("j", NatType(), Eqn(Call("Rsq", i, j),
            Apply(Qualified("Matrix", "map"),
                Apply(Qualified("Matrix", "submatrix"), Call("R", i, j), Qualified("Fin", "cast"), Call("id")), cast))));
    }

    private static Formula ClaimBody()
    {
        var i = V("i"); var j = V("j"); var mu = V("mu"); var n = V("n");
        var sqrt = Apply(Qualified("Real", "sqrt"), D(2));
        var matrix = Apply(Qualified("Matrix", "map"), Call("Rsq", i, j), Qualified("Complex", "ofReal"));
        var root = Ex("n", NatType(), And(Less(D(0), n), Eqn(Pow(
            new Formula.Fraction(mu, Apply(Qualified("Complex", "ofReal"), sqrt)), n), D(1))));
        var spectrum = All("mu", ComplexType(), Imp(Mem(mu, Call("spectrum", ComplexType(), matrix)), root));
        var scaled = Apply(Qualified("SMul", "smul"), Apply(Qualified("Inv", "inv"), sqrt), Call("Rsq", i, j));
        var order = Eqn(Call("orderOf", Parenthesized(scaled)), Mul(D(2), Apply(Qualified("Nat", "lcm"), D(4),
            Apply(Qualified("Nat", "lcm"), Sub(i, j), Add(i, j)))));
        return All("i", NatType(), All("j", NatType(), Imp(Leq(D(1), j), Imp(Less(j, i), And(spectrum, order)))));
    }
}
