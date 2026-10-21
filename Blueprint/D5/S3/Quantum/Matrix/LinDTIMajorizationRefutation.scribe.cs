using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class LinDTIMajorizationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumContext/lin2017dtimajorization");
    private const string Quote = "Let A and B be n × n positive semidefinite matrices. Then λ(A² + |BA|^p) ≻ λ(A² + |AB|^p) for all p > 0.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lin's majorization conjecture fails for positive semidefinite three-by-three matrices at exponent four.",
        H("A counterexample to Lin's Conjecture 4.3"),
        Blocks(
            Node("eigDesc", "Descending eigenvalues", EigDescBody(),
                "Section 2, arXiv v1 p. 2: “For an n × n matrix A with all eigenvalues real, we denote the vector of eigenvalues by λ(A) = (λ₁(A), …, λ_n(A)), and we assume that the components of λ(A) are in descending order.” Hermitian eigenvalues are counted with multiplicity by List.ofFn and sorted in descending order. The list is empty for a non-Hermitian matrix. Each matrix used in the refutation is Hermitian.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Majorizes", "Majorization of descending lists", MajorizesBody(),
                "Section 2, arXiv v1 p. 2: “we say that x weakly majorizes y, written as x ≻_w y, if Σ_{i=1}^k x↓_i ≥ Σ_{i=1}^k y↓_i for k = 1, …, n. We say x majorizes y, denoted by x ≻ y, if x ≻_w y and the sum of all elements of x equal to the sum of all elements of y.” Here x and y are descending eigenvalue lists of equal length; take selects a prefix and sum adds its entries.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 4.3", Disp(Equal(F.Id("claim"), Parenthesized(ClaimBody()))),
                "Conjecture 4.3, arXiv v1 p. 6: “" + Quote + "” The matrix carrier is Matrix (Fin n) (Fin n) ℂ, n ranges over all natural numbers, PosSemidef is positive semidefiniteness, and p ranges over all positive real numbers. cfc and CFC.sqrt express the absolute powers by the real function x ↦ x^p on the positive square root of XᴴX; eigDesc and Majorizes express descending eigenvalues and majorization.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Refutation in dimension three", Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "Use A = diagonal(3,1,1/2) and B = [[1/2,1/4,3/4],[1/4,3/4,0],[3/4,0,5/2]], and p = 4. Rational triangular factorizations prove that B and L − (7/5)I are positive semidefinite, where L = A² + |BA|⁴. The vector (0,−1,19/64) has negative quadratic form for R − (7/5)I, where R = A² + |AB|⁴. Thus every eigenvalue of L is at least 7/5 and an eigenvalue of R is below 7/5. Majorization of the descending three-entry lists would combine its two-entry prefix inequality and equality of the totals to give the opposite ordering of the smallest entries. This contradicts those bounds. No determinant inequality is asserted or refuted here.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lin-2017-majorization-conjecture-4-3"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("linmaj-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Apply(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(F.Id("fun"), Sp, F.Id(name), Sp, Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula N => F.Id("n");
    private static Formula P => F.Id("p");
    private static Formula Mat => Call("Matrix", Call("Fin", N), Call("Fin", N), Complex);
    private static Formula Method(Formula value, string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Parenthesized(value), Dot, F.Id(name))
            : Apply(Seq(Parenthesized(value), Dot, F.Id(name)), args);
    private static Formula Nil => Seq(OpenBracket, CloseBracket);

    private static Formula EigDescBody()
    {
        var m = F.Id("M");
        var h = F.Id("h");
        var list = Apply(Qualified("List", "ofFn"), Method(h, "eigenvalues"));
        var descending = Fn("a", Real, Fn("b", Real, Call("decide", Le(F.Id("b"), F.Id("a")))));
        var body = Seq(F.Id("if"), Sp, h, Sp, Colon, Sp, Method(m, "IsHermitian"), Sp,
            F.Id("then"), Sp, Method(list, "mergeSort", descending), Sp, F.Id("else"), Sp, Nil);
        return Disp(All("n", Nat, All("M", Mat, Equal(Call("eigDesc", m), Parenthesized(body)))));
    }

    private static Formula MajorizesBody()
    {
        var x = F.Id("x");
        var y = F.Id("y");
        var k = F.Id("k");
        var prefix = All("k", Nat, Imp(Le(D(1), k), Imp(Le(k, Method(x, "length")),
            Le(Method(Method(y, "take", k), "sum"), Method(Method(x, "take", k), "sum")))));
        var body = And(prefix, Equal(Method(x, "sum"), Method(y, "sum")));
        return Disp(All("x", Call("List", Real), All("y", Call("List", Real),
            Equal(Call("Majorizes", x, y), Parenthesized(body)))));
    }

    private static Formula ClaimBody()
    {
        var a = F.Id("A");
        var b = F.Id("B");
        Formula Spectrum(Formula product) => Call("eigDesc", Add(new Formula.Power(a, D(2)), Call("cfc", Fn("x", Real, new Formula.Power(F.Id("x"), P)),
            Apply(Qualified("CFC", "sqrt"), Multiply(Call("conjTranspose", product), product)))));
        return All("n", Nat, All("A", Mat, All("B", Mat,
            Imp(Method(a, "PosSemidef"), Imp(Method(b, "PosSemidef"), All("p", Real,
                Imp(Lt(D(0), P), Call("Majorizes", Spectrum(Multiply(b, a)), Spectrum(Multiply(a, b))))))))));
    }
}
