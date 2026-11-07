using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class HannaA078122TernaryCoefficientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/HannaA078122TernaryCoefficient.";
    private static LibraryNoteRef Source() => LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2002a078122");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cubic-shift matrix exists, and every such natural-valued matrix satisfies Hanna's full ternary coefficient formula.",
        H("Hanna's ternary coefficient formula"),
        Blocks(
            Node("hanna-source-matrix", "The cubic-shift source matrix", "IsSourceMatrix", Disp(SourceFormula()),
                "OEIS A078122 revision 10, NAME (unpaginated), states: “Infinite lower triangular matrix, M, that satisfies [M^3](i,j) = M(i+1,j+1) for all i,j>=0 where [M^n](i,j) denotes the element at row i, column j, of the n-th power of matrix M, with M(0,k)=1 and M(k,k)=1 for all k>=0.” Its first-row condition conflicts with lower triangularity. Both source programs instead set the first column to one, as does the displayed matrix. IsSourceMatrix uses this first-column condition and the stated diagonal condition. Finite principal blocks carry Mathlib's ordinary matrix multiplication and third power. Requiring the equation on every block gives the coefficientwise infinite matrix equation because lower triangularity restricts every nonzero summand to the interval between its two indices.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("hanna-partition-series", "The ternary partition reciprocal", "partitionSeries", Disp(SeriesFormula()),
                "The second FORMULA of OEIS A078122 revision 10 (unpaginated) states: “M(n, k) = the coefficient of x^(3^n - 3^(n-k)) in the power series expansion of 1/Product_{j=0..n-k}(1-x^(3^j)) whenever 0<=k<n for all n>0 (conjecture).” Here d=n−k, X is the formal power-series variable, and the finite product ranges over j=0,…,d. Every exponent 3^j is positive, so the denominator has constant coefficient one and its inverse is a formal reciprocal over Rat.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("hanna-claim", "The full second FORMULA conjecture", "claim", Disp(Iff(Call("claim"), ClaimBody())),
                "OEIS A078122 revision 10, second FORMULA (unpaginated), states: “M(n, k) = the coefficient of x^(3^n - 3^(n-k)) in the power series expansion of 1/Product_{j=0..n-k}(1-x^(3^j)) whenever 0<=k<n for all n>0 (conjecture).” The statement includes existence of a natural-valued source matrix and quantifies over every such matrix. The indices n and k are natural numbers, so 0≤k is automatic. The guards 0<n and k<n make both displayed natural subtractions agree with the nonnegative integer exponents in the source. Entries are cast to Rat before comparison with formal coefficients.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("hanna-result", "The coefficient formula for every source matrix", "result", Disp(ClaimBody()),
                "The finite-difference recurrence for the restricted ternary partition coefficients gives a scaled convolution identity by double induction. The resulting natural-valued lower triangular matrices form an additive semigroup in their scale parameter. At parameter one, the cube shifts both indices, while the first column and diagonal are one. Strong induction on rows identifies every source matrix with this construction. The exponent identity 3^(n−k)(3^k−1)=3^n−3^(n−k) gives exactly the stated coefficient. This proves the full unbounded ternary array, including existence; other bases and row-sum interpretations are separate questions.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source())))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula X(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(X(name))) : App(Seq(Operatorname, Grp(X(name))), args);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula NatType() => Call("Nat");
    private static Formula RatType() => Call("Rat");
    private static Formula MatrixType() => Call("Matrix", NatType(), NatType(), NatType());
    private static Formula SeriesType() => Call("PowerSeries", RatType());
    private static Formula FinType(Formula size) => Call("Fin", size);
    private static Formula Add(Formula left, Formula right) => Seq(left, Plus, right);
    private static Formula Sub(Formula left, Formula right) => Parenthesized(Seq(left, Minus, right));
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Fun(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Call("fun"), Parenthesized(Seq(X(name), Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Val(Formula value) => Call("val", value);

    private static Formula SourceBody(Formula matrix)
    {
        Formula n = X("n"), m = X("m"), i = X("i"), j = X("j");
        Formula indexType = FinType(Add(m, D(1)));
        Formula inclusion = Fun("a", indexType, Val(X("a")));
        Formula block = App(Qualified("Matrix", "submatrix"), matrix, inclusion, inclusion);
        Formula shift = All("m", NatType(), All("i", indexType, All("j", indexType,
            Equal(App(Power(block, D(3)), i, j), App(matrix, Add(Val(i), D(1)), Add(Val(j), D(1)))))));
        return And(App(Qualified("Matrix", "IsLowerTriangular"), matrix),
            And(All("n", NatType(), Equal(App(matrix, n, D(0)), D(1))),
                And(All("n", NatType(), Equal(App(matrix, n, n), D(1))), shift)));
    }

    private static Formula SourceFormula() => All("M", MatrixType(),
        Iff(Call("IsSourceMatrix", X("M")), SourceBody(X("M"))));

    private static Formula SeriesFormula()
    {
        Formula d = X("d"), j = X("j");
        Formula one = Parenthesized(Seq(D(1), Colon, Sp, SeriesType()));
        Formula factor = Sub(one, Power(Qualified("PowerSeries", "X"), Power(D(3), j)));
        Formula product = Seq(new Formula.Subscript(Prod, Seq(j, Sp, InMacro, Sp,
            App(Qualified("Finset", "range"), Add(d, D(1))))), Sp, factor);
        return All("d", NatType(), Equal(Call("partitionSeries", d), Power(product, Seq(Minus, D(1)))));
    }

    private static Formula ClaimBody()
    {
        Formula matrix = X("M"), n = X("n"), k = X("k");
        Formula entry = Parenthesized(Seq(App(matrix, n, k), Colon, Sp, RatType()));
        Formula degree = Sub(Power(D(3), n), Power(D(3), Sub(n, k)));
        Formula coefficient = App(Qualified("PowerSeries", "coeff"), degree, Call("partitionSeries", Sub(n, k)));
        return And(Exists("M", MatrixType(), Call("IsSourceMatrix", matrix)),
            All("M", MatrixType(), Imp(Call("IsSourceMatrix", matrix),
                All("n", NatType(), All("k", NatType(), Imp(Less(D(0), n), Imp(Less(k, n), Equal(entry, coefficient))))))));
    }
}
