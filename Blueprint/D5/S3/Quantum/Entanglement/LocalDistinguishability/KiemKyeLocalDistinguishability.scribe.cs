using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.LocalDistinguishability;

internal sealed class KiemKyeLocalDistinguishabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumContext/kiemkye2026localgeometry");
    private const string LocalQuote = "Suppose that closed convex sets C and D with the inclusion C ⊃ D share a boundary point x₀. We say that C ⊃ D is locally distinguishable around x₀ if the set N ∩ (C∖D) is nonempty for every neighborhood N of x₀.";
    private const string ClaimQuote = "For non-generic cases, we cannot show the existence of Schmidt number witnesses around ϱ_{E⊥} by the method in this paper. Nevertheless, we conjecture that the inclusion BP_ℓ ⊋ BP_{ℓ+1} is locally distinguishable around ϱ_{E⊥} for ℓ ≥ k, whenever ϱ_{E⊥} is on the boundary of the convex set BP_k.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent trace-one blockpositive sets are locally distinguishable at every boundary projection state.",
        H("Local distinguishability at boundary projection states"),
        Blocks(
            Paragraph(Text("Complex vectors have coordinates Fin m × Fin n. Operators are Matrix (Fin m × Fin n) (Fin m × Fin n) Complex. EuclideanSpace supplies the Hilbert norm. The imported schmidtRank is the rank of the coefficient matrix with entry x(i,j). Matrix.mulVec is matrix-vector multiplication, dotProduct is the coordinate sum, star is coordinatewise conjugation, and Complex.re is the real part. The topology is the finite-dimensional matrix topology.")),
            Node("ambient", "The trace-one Hermitian affine space", AmbientFormula(),
                "Section 3, page 7, uses the affine subspace H of Hermitian matrices with trace one. Both conditions are included."),
            Node("BP", "The blockpositive sets", BPFormula(),
                "Section 3, page 7: “A Hermitian matrix W ∈ M_m ⊗ M_n is called k-blockpositive if ⟨ξ|W|ξ⟩ ≥ 0 for every |ξ⟩ with SR |ξ⟩ ≤ k.” BP restricts this condition to the trace-one affine space. For Hermitian W the quadratic form is real, so the displayed real-part inequality is the same condition."),
            Node("rhoPerp", "A normalized orthogonal projection", RhoFormula(),
                "Sections 3 and 5 write ϱ_{E⊥} for the projection state onto E⊥. Submodule.starProjection is orthogonal projection, Matrix.toEuclideanLin.symm gives its coordinate matrix, and the inverse of the complex dimension normalizes its trace when E is proper. The definition also has a value for E equal to the whole space, where the dimension is zero; that case is excluded from the conclusion."),
            Node("OnBoundary", "Boundary relative to the affine space", BoundaryFormula(),
                "The boundary is relative to the trace-one Hermitian space. The set BP is closed there: it is the intersection of the closed nonnegative quadratic-form tests. Thus the two membership conditions express the relative boundary."),
            Node("LocallyDistinguishable", "Every neighbourhood meets the difference", LocalFormula(),
                "Section 2, page 6: “" + LocalQuote + "” The predicate displays the neighbourhood condition; the source's standing geometric conditions hold for the sets and states in the conclusion. Ambient matrix neighbourhoods give the same condition as relative neighbourhoods because the difference lies in H."),
            Node("claim", "The Kiem–Kye conjecture", Equivalent(X("claim"), ClaimBody()),
                "Section 5, page 12: “" + ClaimQuote + "” Here m and n are the local dimensions, E is nonzero and proper, k and l are natural numbers with 1 ≤ k ≤ l < min(m,n), and rhoPerp(E) is ϱ_{E⊥}. These bounds are the range of adjacent sets in the source's finite chain. No genericity assumption is imposed."),
            Describe.Lean(DescribeId.Create("kiem-kye-local-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Local distinguishability for every subspace"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("A positive semidefinite matrix on the boundary has a unit kernel vector of Schmidt rank at most k. Compactness of the unit low-rank vectors makes the projection of the nonpositive quadratic-form tests closed, which supplies this kernel vector at a boundary limit.")),
                    Paragraph(Text("A rank-one perturbation raises a rectangular coefficient matrix's rank by one: a dual vector nonzero on its kernel is paired with a vector outside its range. Rank–nullity identifies the new kernel as the intersection of two kernels. Repetition and normalization place the old unit vector in the closure of the unit vectors of rank l+1.")),
                    Paragraph(Text("Compression by I−uu† moves the kernel to u while preserving positivity. Its trace tends to one near the original kernel vector, so normalized compression is continuous there. For each unit u of rank l+1, compactness gives an overlap bound α<1 on unit vectors of rank at most l. The matrix Q=αI−uu† is nonnegative on all those vectors and negative at u. Adding a small positive multiple of Q to the compressed state and normalizing the trace produces a matrix in BP_l outside BP_(l+1). Two closure arguments return to the original state. The same sufficient condition applies to any positive semidefinite trace-one matrix with a unit kernel vector of Schmidt rank at most l+1. No convergence rate or converse characterization is asserted."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kiem-kye-2026-local-distinguishability"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("kiem-kye-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula At(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula Call(string name, params Formula[] args) => At(Seq(Operatorname, Grp(X(name))), args);
    private static Formula QCall(string owner, string name, params Formula[] args) => At(Qualified(owner, name), args);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(X(name), Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula EqualTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Unequal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Equivalent(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Difference(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Setminus, Sp, b));
    private static Formula Index() => Parenthesized(Seq(Call("Fin", X("m")), Sp, Times, Sp, Call("Fin", X("n"))));
    private static Formula MatrixType() => Call("Matrix", Index(), Index(), X("Complex"));
    private static Formula VectorType() => new Formula.TypeArrow(Index(), X("Complex"));
    private static Formula SubspaceType() => Call("Submodule", X("Complex"), Call("EuclideanSpace", X("Complex"), Index()));
    private static Formula Dims(Formula body) => All("m", X("Nat"), All("n", X("Nat"), body));
    private static Formula Ambient() => Call("ambient", X("m"), X("n"));
    private static Formula BP(Formula k) => Call("BP", X("m"), X("n"), k);
    private static Formula RhoE() => Call("rhoPerp", X("E"));
    private static Formula AmbientFormula() => Dims(EqualTo(Ambient(),
        Seq(OpenBrace, X("W"), Colon, Sp, MatrixType(), Sp, Mid, Sp,
            And(QCall("Matrix", "IsHermitian", X("W")), EqualTo(QCall("Matrix", "trace", X("W")), D(1))), CloseBrace)));
    private static Formula BPFormula()
    {
        var expectation = QCall("Complex", "re", Call("dotProduct", Call("star", X("x")),
            QCall("Matrix", "mulVec", X("W"), X("x"))));
        var tests = All("x", VectorType(), Imp(Le(Call("schmidtRank", X("x")), X("k")), Le(D(0), expectation)));
        var set = Seq(OpenBrace, X("W"), Colon, Sp, MatrixType(), Sp, Mid, Sp,
            And(Member(X("W"), Ambient()), tests), CloseBrace);
        return Dims(All("k", X("Nat"), EqualTo(BP(X("k")), set)));
    }
    private static Formula RhoFormula()
    {
        var perp = new Formula.Power(X("E"), Perp);
        var projection = Seq(perp, Dot, Operatorname, Grp(X("starProjection")), Dot, Operatorname, Grp(X("toLinearMap")));
        var dimension = Parenthesized(Seq(QCall("Module", "finrank", X("Complex"), perp), Colon, Sp, X("Complex")));
        var inverse = new Formula.Power(dimension, new Formula.Negate(D(1)));
        var conversion = Seq(Qualified("Matrix", "toEuclideanLin"), Dot, Operatorname, Grp(X("symm")));
        return Dims(All("E", SubspaceType(), EqualTo(RhoE(), QCall("SMul", "smul", inverse, At(conversion, projection)))));
    }
    private static Formula BoundaryFormula() => Dims(All("k", X("Nat"), All("rho", MatrixType(),
        Equivalent(Call("OnBoundary", X("m"), X("n"), X("k"), X("rho")),
            And(Member(X("rho"), BP(X("k"))), Member(X("rho"), Call("closure", Difference(Ambient(), BP(X("k"))))))))));
    private static Formula LocalFormula()
    {
        var meets = QCall("Set", "Nonempty", QCall("Set", "inter", X("N"), Difference(X("C"), X("D"))));
        var body = All("N", Call("Set", MatrixType()), Imp(Member(X("N"), Call("nhds", X("x"))), meets));
        return Dims(All("C", Call("Set", MatrixType()), All("D", Call("Set", MatrixType()),
            All("x", MatrixType(), Equivalent(Call("LocallyDistinguishable", X("C"), X("D"), X("x")), body)))));
    }
    private static Formula ClaimBody() => Dims(All("E", SubspaceType(),
        Imp(Unequal(X("E"), Qualified("Bot", "bot")), Imp(Unequal(X("E"), Qualified("Top", "top")),
            All("k", X("Nat"), All("l", X("Nat"),
                Imp(Le(D(1), X("k")), Imp(Le(X("k"), X("l")),
                    Imp(Less(X("l"), Call("min", X("m"), X("n"))),
                        Imp(Call("OnBoundary", X("m"), X("n"), X("k"), RhoE()),
                            Call("LocallyDistinguishable", BP(X("l")), BP(Add(X("l"), D(1))), RhoE())))))))))));
}
