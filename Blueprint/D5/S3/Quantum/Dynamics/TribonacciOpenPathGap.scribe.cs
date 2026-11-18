using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class TribonacciOpenPathGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/TribonacciOpenPathGap.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every fixed real rho between zero and one, the minimum absolute eigenvalue "
        + "of the actual positive Tribonacci even open prefixes tends to zero along all levels.",
        H("Vanishing spectral distance for positive Tribonacci open chains"),
        Blocks(
            Paragraph(Text("Use the literal A-starting word W for A to AB, B to AC, C to A. "
                + "TribonacciPrefixRefutation supplies the original weights A=2, B=1, C=0, "
                + "the recursive words U(0)=empty and U(n+1)=sigma^(4(n+1))(C) U(n), "
                + "their exact occurrence at position zero, and their closed alternating charge. "
                + "TribonacciAlignedWindows supplies L(j)=length(sigma^j(A)) and N(j)=2 floor(L(j)/2).")),
            Node("alternatingCharge", "alternating-charge", "Alternating integer charge", DescribeRole.Definition,
                All("a", Arrow(Nat(), Int()), All("k", Nat(), Eq(Call("alternatingCharge", X("a"), X("k")),
                    Call("alternatingSum", Call("map", X("a"), Call("range", X("k"))))))),
                "For a natural-indexed integer sequence a, the charge of k entries is "
                + "a(0)-a(1)+a(2)-... with exactly k terms. The empty charge is zero."),
            Node("green_charge", "exponential-green", "The exact exponential Green entry", DescribeRole.Theorem,
                GreenFormula(),
                "For every real rho different from zero, every integer sequence a and every natural q, "
                + "the original greenEntry at start zero and displacement q equals rho raised to the "
                + "negative alternating charge of exactly 2q+1 entries. Integer powers allow arbitrary "
                + "signs of a. The proof inducts on q using the original Green recursion and "
                + "alternatingSum_append. It establishes the odd-over-even ratio, including the final "
                + "even bond in the denominator; the reciprocal ratio has the opposite charge sign."),
            Node("openPath", "positive-open-path", "The actual finite open-chain matrix", DescribeRole.Definition,
                PathFormula(),
                "Here t maps natural indices to real hoppings, m is natural, and i,j lie in Fin(2m). "
                + "The real entries displayed in the formula are cast to complex numbers. "
                + "There are 2m sites, zero diagonal and exactly 2m-1 bonds when m is positive. "
                + "The last physical bond is t(2m-2); there is no boundary-to-boundary bond."),
            Node("hopping", "tribonacci-hopping", "Positive Tribonacci hoppings", DescribeRole.Definition,
                All("r", Real(), All("i", Nat(), Eq(Call("hopping", X("r"), X("i")),
                    Pow(X("r"), Call("weight", Call("W", X("i"))))))),
                "For 0<rho<1 every hopping is positive. The values are exactly rho squared on A, "
                + "rho on B and one on C. Integer powers agree with these nonnegative natural powers."),
            Node("absEigenvalues", "absolute-eigenvalues", "The finite absolute eigenvalue set", DescribeRole.Definition,
                AbsoluteEigenvalueFormula(),
                "The Hermitian matrix is openPath(hopping(rho), floor(L(j)/2)), acting on Fin(N(j)). "
                + "Its real spectrum is the range of its real eigenvalue function. The finite image "
                + "therefore equals the set of absolute values of that spectrum. For j>=1, "
                + "iterate_growth gives L(j)>=j+1>=2, so this set is nonempty."),
            Node("gap", "minimum-distance", "Minimum absolute eigenvalue", DescribeRole.Definition,
                All("r", Real(), All("j", Nat(), Eq(Call("gap", X("r"), X("j")),
                    Call("ite", Le(D(1), X("j")), Call("min", Call("absEigenvalues", X("r"), X("j"))), D(0))))),
                "For j>=1 this is the minimum of the finite nonempty absolute eigenvalue set, "
                + "hence precisely the single-particle distance from zero energy. The value at j=0 "
                + "is defined as zero and has no effect on the limit."),
            Node("gap_tendsto_zero", "all-prefix-limit", "The limit along every actual even iterate prefix", DescribeRole.Theorem,
                All("r", Real(), Implies(And(Lt(D(0), X("r")), Lt(X("r"), D(1))),
                    Call("Tendsto", Call("gap", X("r")), Call("atTop"), Call("nhds", D(0))))),
                "For every fixed rho in (0,1), gap(rho,j) tends to zero as j tends to infinity. "
                + "The quantifier is over the entire deterministic sequence N(j), without selecting "
                + "a subsequence or replacing the endpoints by periodic boundaries."),
            Paragraph(Text("To connect the original inverse to positive hoppings, let D be diagonal "
                + "with D(i,i)=(-1)^i. The positive lower bidiagonal block C is D lowerBlock(t,m) D. "
                + "Its diagonal is t(2i), its subdiagonal is positive t(2i-1), and D squared is I. "
                + "The original block_inverse and greenMatrix give C inverse as D greenMatrix(t,m) D. "
                + "Reordering actual sites into evens and odds produces the block matrix [0,C;C transpose,0]. "
                + "The explicit parity bijection sends inl(i) to 2i and inr(i) to 2i+1. "
                + "For q<m the absolute value of the full inverse entry in row 2q+1, column zero is "
                + "greenEntry(t,0,q). Every used bond has index at most 2q, so no artificial boundary bond enters.")),
            Paragraph(Text("All matrix norms in the spectral step are the L2 operator norm on complex "
                + "Euclidean coordinate spaces. The original arbitrary-dimension entry_le_norm bounds "
                + "this inverse entry by the full inverse norm. Pinned Mathlib's "
                + "CStarAlgebra.norm_or_neg_norm_mem_spectrum, spectrum inverse-unit correspondence, "
                + "Matrix.IsHermitian.inv and spectrum_real_eq_range_eigenvalues supply the spectral conversion. "
                + "Thus the actual matrix has a real spectral value of absolute value at most the "
                + "reciprocal Green entry. Positive diagonal entries make the bidiagonal block and "
                + "the full even chain nonsingular.")),
            Paragraph(Text("Induction using four_odd gives length(U(n)) congruent to n modulo two. "
                + "For odd n write length(U(n))=2q+1. The original prefixWord_actual and "
                + "prefixCharge_closed give charge(U(n))=(n+1)(n+2). Consequently, whenever "
                + "N(j)>=length(U(n))+1, the full-chain inverse entry has magnitude "
                + "rho^(-(n+1)(n+2)), and the spectral distance is at most rho^((n+1)(n+2)). "
                + "The inequality N(j)>=length(U(n))+1 is exactly what ensures q<L(j)/2.")),
            new DocumentBlock.DisplayFormula(EpsilonFormula()),
            Paragraph(Text("Given epsilon>0, choose k with rho^k<epsilon and take the fixed odd "
                + "level n=2k+1. Since (n+1)(n+2)>=k, its spectral bound is below epsilon. "
                + "The original iterate_growth implies N(j)>=length(U(n))+1 for every sufficiently "
                + "large j. This proves the displayed epsilon formulation along all j>=J. "
                + "For a finite nonempty real spectrum, its minimum absolute value is below epsilon "
                + "if and only if some real spectral value has absolute value below epsilon; "
                + "nonnegativity then gives the stated limit.")),
            Paragraph(Text("The conclusion concerns the original open chain with positive hoppings: "
                + "for any fixed 0<rho<1, the minimum absolute eigenvalue tends to zero along the full "
                + "sequence of lengths N(j) rounded down to even integers. The proof uses the original "
                + "actual prefixes and closed charge formula, retains all external sites, and connects "
                + "the full inverse matrix through a parity coordinate permutation and alternating-sign "
                + "conjugation. First fix an odd-level prefix satisfying the error requirement, then use "
                + "growth of the actual iterate lengths to cover every sufficiently large j; thus no "
                + "subsequence replaces the full sequence.")),
            Paragraph(Text("This is a consequence for the specified finite single-particle matrices. "
                + "It supplies no uniform rate in N, matching lower rate, entropy or filling law, "
                + "many-body excitation gap, infinite-volume spectral statement or physical realization. "
                + "No literature novelty or external open-problem resolution is asserted.")))));

    private static Formula AbsoluteEigenvalueFormula()
    {
        Formula eigenvalue = Call("eigenvalues", Hamiltonian(X("r"), X("j")), X("i"));
        Formula indexType = Call("Fin", Call("N", X("j")));
        Formula values = Call("image", Lam("i", indexType, Call("abs", eigenvalue)), Call("univ"));
        return All("r", Real(), All("j", Nat(), Eq(Call("absEigenvalues", X("r"), X("j")), values)));
    }
    private static Formula GreenFormula()
    {
        Formula t = Lam("i", Nat(), Pow(X("r"), App(X("a"), X("i"))));
        return All("r", Real(), Implies(Ne(X("r"), D(0)), All("a", Arrow(Nat(), Int()),
            All("q", Nat(), Eq(Call("greenEntry", t, D(0), X("q")),
                Pow(X("r"), new Formula.Negate(
                    Call("alternatingCharge", X("a"), Add(Mul(D(2), X("q")), D(1))))))))));
    }
    private static Formula PathFormula()
    {
        Formula i = X("i"), j = X("j"), m = X("m"), t = X("t");
        Formula iv = Call("val", i), jv = Call("val", j);
        return All("t", Arrow(Nat(), Real()), All("m", Nat(),
            All("i", Call("Fin", Mul(D(2), m)), All("j", Call("Fin", Mul(D(2), m)),
                Eq(Call("openPath", t, m, i, j), Call("ite", Eq(Add(iv, D(1)), jv),
                    Call("complex", App(t, iv)), Call("ite", Eq(Add(jv, D(1)), iv),
                        Call("complex", App(t, jv)), D(0))))))));
    }
    private static Formula EpsilonFormula() => All("r", Real(),
        Implies(And(Lt(D(0), X("r")), Lt(X("r"), D(1))), All("e", Real(),
            Implies(Lt(D(0), X("e")), Some("J", Nat(), And(Le(D(1), X("J")),
                All("j", Nat(), Implies(Le(X("J"), X("j")), Some("x", Real(),
                    And(new Formula.Relation(X("x"), FormulaRelationOperator.MemberOf,
                        Call("spectrum", Real(), Hamiltonian(X("r"), X("j")))),
                        Lt(Call("abs", X("x")), X("e"))))))))))));
    private static Formula Hamiltonian(Formula r, Formula j) =>
        Call("openPath", Call("hopping", r), Call("floorhalf", Call("L", j)));
    private static DocumentBlock Node(string name, string id, string title, DescribeRole role,
        Formula formula, string prose) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(F.Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula X(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Int() => Seq(Mathbb, Grp(X("Z")));
    private static Formula Real() => Seq(Mathbb, Grp(X("R")));
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [..xs]);
    private static Formula Call(string name, params Formula[] xs) => App(X(name), xs);
    private static Formula Lam(string v, Formula type, Formula body) =>
        Seq(Open, X(v), Colon, Sp, type, Close, Sp, Mapsto, Sp, Open, body, Close);
    private static Formula All(string v, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), t, b);
    private static Formula Some(string v, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
}
