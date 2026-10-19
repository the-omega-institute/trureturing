using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class LiTanCirculantPositivityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/LiTanCirculantPositivityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/litan2024bargmann");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Li–Tan circulant transform of a positive semidefinite correlation matrix can have a negative quadratic value at order four.",
        H("Li–Tan circulant positivity fails at order four"), Blocks(
            Paragraph(Text("Indices are in Fin n, with addition modulo n. Matrix positivity uses Matrix.PosSemidef. "
                + "Complex.arg takes values in (−π, π], and the real power of the nonnegative modulus product uses Real.rpow. "
                + "The matrix with entry 1 when j=i+1 and 0 otherwise is the source's C_n. "
                + "The displayed real and complex type annotations show the scalar coercions.")),
            Entry("coefficients", "z", "Geometric moduli and mean principal phases", CoefficientFormula(),
                "Section III, page 5: \"For each H = (h_kl) ∈ Mat_{n×n}(ℂ), we can associate it with a circulant matrix C_H = Σ_{k=0}^{n−1} z_k C_nᵏ, where the coefficients are given by z_k = (Π_{l=1}^n r_{l(l⊕k)})^{1/n} e^{iθ_k}, with θ_k := (Σ_{l=1}^n θ_{l(l⊕k)})/n and h_kl = r_kl e^{iθ_kl}, where r_kl ≥ 0 and θ_kl ∈ (−π, π].\" Here r_kl is ‖H k l‖ and θ_kl is Complex.arg (H k l). The natural k becomes Fin.ofNat n k before addition to l. Products and sums run over every l : Fin n exactly once.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("transform", "CH", "The associated circulant matrix", TransformFormula(),
                "Section II, page 2: \"Let C_n = G_{(0,1,0,…,0)}\". Section III, page 5: \"For each H = (h_kl) ∈ Mat_{n×n}(ℂ), we can associate it with a circulant matrix C_H = Σ_{k=0}^{n−1} z_k C_nᵏ, where the coefficients are given by z_k = (Π_{l=1}^n r_{l(l⊕k)})^{1/n} e^{iθ_k}, with θ_k := (Σ_{l=1}^n θ_{l(l⊕k)})/n and h_kl = r_kl e^{iθ_kl}, where r_kl ≥ 0 and θ_kl ∈ (−π, π].\" The shift matrix is written entrywise. HSMul.hSMul is scalar multiplication, the exponent k is natural, and k ∈ Finset.range n means 0 ≤ k < n.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("conjecture", "claim", "The positivity conjecture", Disp(Equal(V("claim"), Parenthesized(ClaimBody()))),
                "Section II, page 2: \"Let 𝐇_n denote the set of all n × n Hermitian matrices H that are positive semidefinite and have h_ii = 1 for all i = 1, …, n.\" Section III, page 5: \"For the case when n = 3, we deduced that the positive semidefiniteness of C_H follows from the positive semidefiniteness of H. This leads us to the conjecture that the positive semidefiniteness of H implies the positive semidefiniteness of C_H (which may depend on n) for general n.\" The formula quantifies over every nonzero natural n and every complex matrix H with positive semidefiniteness and unit diagonal. The source's labels 1,…,n are represented by Fin n.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("refutation", "result", "A rational counterexample of order four", Disp(Seq(Neg, Sp, Parenthesized(ClaimBody()))),
                "Take H with rows (1,5/8,1/9,5/8), (5/8,1,5/8,4/9), (1/9,5/8,1,5/8), and (5/8,4/9,5/8,1). "
                + "A diagonal Gram factorization proves H.PosSemidef, and its diagonal entries are 1. Every entry is a positive real number, so every principal phase is zero. "
                + "The coefficients are (1,5/8,2/9,5/8). Thus CH 4 H has these entries as its first row, and its quadratic value at (1,−1,1,−1) is −1/9. "
                + "Positivity would force this value to be nonnegative. Unequal opposite correlations 1/9 and 4/9 become their geometric mean 2/9. "
                + "This refutes the general implication already for real matrices at n=4. The argument makes no assertion about the source's n=3 result or the separate equality of the two Bargmann invariant sets.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula CoefficientFormula()
    {
        Formula n = V("n"), h = V("H"), k = V("k"), l = V("l");
        Formula entry = App(h, l, Add(l, App(Q("Fin", "ofNat"), n, k)));
        Formula moduli = Seq(new Formula.Subscript(Prod, Seq(l, Colon, Sp, Call("Fin", n))), Sp, new Formula.Norm(entry));
        Formula phases = Seq(new Formula.Subscript(Sum, Seq(l, Colon, Sp, Call("Fin", n))), Sp, App(Q("Complex", "arg"), entry));
        Formula magnitude = new Formula.Power(Parenthesized(moduli), new Formula.Fraction(Typed(D(1), Real()), Typed(n, Real())));
        Formula phase = App(Q("Complex", "exp"), Mul(Q("Complex", "I"), Typed(new Formula.Fraction(phases, Typed(n, Real())), Complex())));
        return Disp(All("n", Nat(), WithNonzero(n, All("H", Matrix(n), All("k", Nat(),
            Equal(Call("z", n, h, k), Mul(Typed(magnitude, Complex()), phase)))))));
    }

    private static Formula TransformFormula()
    {
        Formula n = V("n"), h = V("H"), k = V("k"), i = V("i"), j = V("j");
        Formula shift = App(Q("Matrix", "of"), Parenthesized(Seq(V("fun"), Sp,
            Parenthesized(Seq(i, Sp, j, Colon, Sp, Call("Fin", n))), Sp, Mapsto, Sp,
            V("if"), Sp, Equal(j, Add(i, D(1))), Sp, V("then"), Sp, Typed(D(1), Complex()),
            Sp, V("else"), Sp, D(0))));
        Formula sum = Seq(new Formula.Subscript(Sum, Member(k, App(Q("Finset", "range"), n))), Sp,
            App(Q("HSMul", "hSMul"), Call("z", n, h, k), new Formula.Power(shift, k)));
        return Disp(All("n", Nat(), WithNonzero(n, All("H", Matrix(n), Equal(Call("CH", n, h), sum)))));
    }

    private static Formula ClaimBody()
    {
        Formula n = V("n"), h = V("H"), i = V("i");
        return All("n", Nat(), WithNonzero(n, All("H", Matrix(n),
            Imp(App(Q("Matrix", "PosSemidef"), h),
                Imp(All("i", Call("Fin", n), Equal(App(h, i, i), D(1))),
                    App(Q("Matrix", "PosSemidef"), Call("CH", n, h)))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
    private static Formula Matrix(Formula n) => Call("Matrix", Call("Fin", n), Call("Fin", n), Complex());
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, body);
    private static Formula WithNonzero(Formula n, Formula body) =>
        Seq(OpenBracket, Call("NeZero", n), CloseBracket, Comma, Sp, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
}
