using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class PositiveFilterTransposeRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/marquezgonzalez2026feasibility");
    private const string WeakQuote = "The weaker question, which is sufficient for the source-placement theorem, asks only whether there exist a positive map ℱ and a completely positive map ℰ such that Υᵀ=ℱ∘Υ∘ℰ.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A unital qutrit measure-and-prepare channel has no factorization of its channel transpose through a positive outer filter and a completely positive inner filter. Nonnegative coefficients impose kernel constraints incompatible with the unital sum and the nonorthogonal state kernels.",
        H("A qutrit obstruction to positive/CP factorization of the channel transpose"),
        Blocks(
            Describe.Remark(DescribeId.Create("physlib-hermitian-preserving"),
                H("Hermitian preservation"),
                Disp(PhyslibHermitianDefinition()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumChannels/meiburg2025physlibdual")),
                Blocks(Paragraph(Text("Let A and B be finite coordinate types and R an RCLike scalar field. MatrixMap(A,B,R) is the space of R-linear maps from square A matrices to square B matrices. A map preserves Hermitian matrices when every Hermitian input has a Hermitian output.")))),
            Describe.Remark(DescribeId.Create("physlib-positive-hermitian"),
                H("Positive maps preserve Hermitian matrices"),
                Disp(PhyslibAll("M", PhyslibMap("A", "B", "R"),
                    PhyslibImp(PhyslibCall("IsPositive", F.Id("M")), PhyslibCall("IsHermitianPreserving", F.Id("M"))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumChannels/meiburg2025physlibdual")),
                Blocks(Paragraph(Text("Let A and B be finite coordinate types and R an RCLike scalar field. Every Hermitian matrix is the difference of its positive and negative parts, both positive semidefinite. A positive linear map sends both parts to positive semidefinite matrices. Their difference is Hermitian.")))),
            Describe.Lean(DescribeId.Create("physlib-cp-positive"),
                DeclarationHandle.Create(Prefix + "IsPositive"),
                H("Complete positivity implies positivity"),
                StatementSource.FromAuthor(Disp(PhyslibAll("M", PhyslibMap("A", "B", "R"),
                    PhyslibImp(PhyslibCall("IsCompletelyPositive", F.Id("M")), PhyslibCall("IsPositive", F.Id("M")))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumChannels/meiburg2025physlibdual")),
                Blocks(Paragraph(Text("Let A and B be finite coordinate types, with decidable equality on A, and let R be an RCLike scalar field. Complete positivity requires positivity after tensoring with the identity map on matrices of every finite size. At size one, the product coordinate types A times Fin 1 and B times Fin 1 identify with A and B. Restricting along those equivalences gives positivity of M itself."))),
                DescribeRole.Theorem),
            Describe.Remark(DescribeId.Create("physlib-trace-dual"),
                H("The trace dual"),
                Disp(PhyslibDualDefinition()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumChannels/meiburg2025physlibdual")),
                Blocks(Paragraph(Text("For finite coordinate types A and B with decidable equality and a commutative ring R, dual M is an R-linear map from B matrices to A matrices. Let betaA and betaB be the standard matrix-basis equivalences with their R-linear dual spaces, and let Mvee be the algebraic dual map. Let tauA and tauB denote matrix transpose. Then dual(M)=tauA composed with betaA inverse, Mvee, betaB, and tauB. No complex conjugation occurs in this definition.")))),
            Describe.Lean(DescribeId.Create("physlib-dual-trace-equality"),
                DeclarationHandle.Create(Prefix + "trace_eq"),
                H("Trace duality"),
                StatementSource.FromAuthor(Disp(PhyslibTraceEquality())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumChannels/meiburg2025physlibdual")),
                Blocks(Paragraph(Text("Let A and B be finite coordinate types with decidable equality, R a commutative ring, and M an R-linear map from A matrices to B matrices. For every input X and output test matrix Y, tr(M(X)Y)=tr(X dual(M)(Y)). In standard coordinates, the pairing with the transposed matrix is exactly the standard-basis dual pairing. The two transposes in the definition convert that coordinate pairing into the trace pairing."))),
                DescribeRole.Theorem),
            Describe.Remark(DescribeId.Create("physlib-dual-hermitian"),
                H("The dual preserves Hermitian matrices"),
                Disp(PhyslibDualPreservation("IsHermitianPreserving")),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumChannels/meiburg2025physlibdual")),
                Blocks(Paragraph(Text("Let A and B be finite coordinate types with decidable equality. For complex matrices, a Hermitian-preserving linear map commutes with conjugate transpose, by decomposing a matrix into its real and imaginary self-adjoint parts. Trace duality and nondegeneracy of the trace pairing then show that its dual also preserves Hermitian matrices.")))),
            Describe.Lean(DescribeId.Create("physlib-positive-trace-product"),
                DeclarationHandle.Create(Prefix + "trace_mul_nonneg"),
                H("Nonnegative trace of a product of positive matrices"),
                StatementSource.FromAuthor(Disp(PhyslibTraceNonnegative())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumChannels/meiburg2025physlibdual")),
                Blocks(Paragraph(Text("Let n be a finite coordinate type with decidable equality and R an RCLike field. For positive semidefinite n by n matrices X and Y over R, tr(XY) is nonnegative in the scalar star order. Factor Y as S adjoint times S. Cyclicity of trace identifies tr(XY) with tr(S X S adjoint), the trace of a positive semidefinite matrix. In the complex case, nonnegativity includes that this trace is real."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("physlib-positive-kernel-sum"),
                DeclarationHandle.Create(Prefix + "ker_sum"),
                H("The kernel of a sum of positive matrices"),
                StatementSource.FromAuthor(Disp(PhyslibKernelSum())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumChannels/meiburg2025physlibdual")),
                Blocks(Paragraph(Text("Let f be any family of Hermitian matrices over an RCLike field, indexed by a finite type I, on a finite coordinate type n with decidable equality. Assume each f(i) is nonnegative in the matrix order. The kernel of their sum, acting on Euclidean coordinate space, is the intersection of their kernels. For a vector killed by the sum, the sum of the nonnegative quadratic forms is zero. Every individual quadratic form is therefore zero, which is equivalent to membership in that matrix's kernel. The reverse inclusion follows by linearity. This identity also covers empty index and coordinate types. For the qutrit decomposition, apply it to f(j)=C(k,j) sigma(j) and cancel the nonzero coefficient C(k,j)."))),
                DescribeRole.Theorem),
            Describe.Remark(DescribeId.Create("physlib-dual-positive"),
                H("The dual of a positive map is positive"),
                Disp(PhyslibDualPreservation("IsPositive")),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumChannels/meiburg2025physlibdual")),
                Blocks(
                    Paragraph(Text("Let A and B be finite coordinate types with decidable equality and M a positive complex linear map from A matrices to B matrices. For a positive semidefinite Y, and any vector v, the quadratic form of dual(M)(Y) at v equals tr(M(v v adjoint)Y). Both factors on the right are positive semidefinite, so this scalar is nonnegative. Hermitian preservation of the dual supplies the other part of the positive semidefinite criterion.")),
                    Paragraph(Text("Applied to a positive diagonal matrix unit, dual positivity and trace duality give positive semidefinite trace representatives of diagonal functionals.")))),
            Describe.Lean(DescribeId.Create("mgposfilt-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("The weak question at dimension three"), StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Section VI, Eq. (48): “" + WeakQuote + "” The dimension-three assertion asks for this factorization for every unital qutrit channel. MatrixMap(Fin 3, Fin 3, complex) consists of complex linear maps on three by three complex matrices. UnitalChannel F means that F is completely positive, preserves the trace of every matrix, and sends the identity matrix to itself. Here F denotes the channel Υ, while P and E denote the filters ℱ and ℰ. IsPositive P means that P sends every positive semidefinite matrix to a positive semidefinite matrix. IsCompletelyPositive E requires the same property for every finite matrix amplification of E by an identity map. Neither filter is required to preserve trace, to be unital, or to be invertible. Composition is equality of complex linear maps, hence holds on every complex matrix.")),
                    Paragraph(Text("The quantifiers include every finite index type S and every Kraus family K representing F; [Fintype S] supplies the finite sum. ofKraus is MatrixMap.of_kraus, with ofKraus(K,K)(X)=∑ᵢ Kᵢ X Kᵢ†. The transposed family is i↦Kᵢᵀ, where transpose is the ordinary matrix transpose in the fixed standard basis. The second formula expands the transpose channel and identifies (Kᵢᵀ)† with the entrywise conjugate K̅ᵢ, denoted map(Kᵢ,star). It therefore gives the channel transpose of Section II.D, Eqs. (15)–(16), rather than the transpose of an output matrix. This channel transpose is independent of the finite Kraus representation and depends on the chosen basis. A counterexample in dimension three refutes the unrestricted unital-qudit assertion.")),
                    Paragraph(Math(Disp(TransposeFormula())))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mgposfilt-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Refutation of the weak question"), StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Let U=(1/7)[[3,−2,6],[6,3,−2],[−2,6,3]], and let uⱼ be its columns and eⱼ the standard basis vectors. Put ρⱼ=(eⱼeⱼ†+uⱼuⱼ†)/2. The matrix U is real orthogonal. These three positive semidefinite matrices each have trace 1 and sum to the identity. The channel F(X)=∑ⱼ Xⱼⱼρⱼ has twelve real Kraus matrices: eⱼeⱼᵀ/2 and uⱼeⱼᵀ/2, each repeated twice for each j. Their finite Kraus sum is F, so F is completely positive; the state traces give trace preservation, and the state sum gives unitality. Its channel transpose is Fᵀ(X)=diag(tr(ρ₀X),tr(ρ₁X),tr(ρ₂X)).")),
                    Paragraph(Text("Suppose Fᵀ=P∘F∘E with P positive and E completely positive. Complete positivity at amplification size one implies that E is positive. For each k and j there are positive semidefinite trace representatives Bₖ and σⱼ with tr(BₖX)=P(X)ₖₖ and tr(σⱼX)=E(X)ⱼⱼ for every X. Write Jₖₖ for a diagonal matrix unit. The representatives are Bₖ=dual(P)(Jₖₖ) and σⱼ=dual(E)(Jⱼⱼ). The dual of a positive map is positive, and tr(M(X)Y)=tr(X dual(M)(Y)); applying these facts to the positive diagonal units gives their positivity and the displayed trace identities. Define Cₖⱼ=P(ρⱼ)ₖₖ=tr(Bₖρⱼ)≥0. Taking the kth diagonal entry of the factorization and using nondegeneracy of the trace pairing gives ρₖ=∑ⱼ Cₖⱼσⱼ. Every Bₖ is nonzero: otherwise the kth coefficient row and hence ρₖ would vanish, contradicting tr(ρₖ)=1.")),
                    Paragraph(Text("If Cₖⱼ=0, the expression tr(Bₖρⱼ)=(eⱼ†Bₖeⱼ+uⱼ†Bₖuⱼ)/2 is a sum of nonnegative quadratic forms equal to zero. Thus Bₖeⱼ=Bₖuⱼ=0. For distinct j and l, the vectors eⱼ,eₗ,uⱼ form a basis. Two different zeros in the kth row would therefore force Bₖ=0. Each row of C has at most one zero.")),
                    Paragraph(Text("The state kernel vectors are v₀=(0,1,3), v₁=(3,0,1), and v₂=(1,3,0). With these columns, V=[[0,3,1],[1,0,3],[3,1,0]] has determinant 28. The diagonal-entry matrix Dₖₐ=(ρₖ)ₐₐ=(1/49)[[29,18,2],[2,29,18],[18,2,29]] has determinant 79/343. Set Tⱼₐ=(σⱼ)ₐₐ. The coefficient relation gives D=CT, so T is nonsingular and no σⱼ is zero. The kernel of a finite sum of positive semidefinite matrices is the intersection of their kernels. Apply this to ρₖ=∑ⱼ Cₖⱼσⱼ and ρₖvₖ=0. It gives Cₖⱼσⱼvₖ=0, hence σⱼvₖ=0 whenever Cₖⱼ≠0. If a column of C had no zero, its σⱼ would annihilate all columns of the invertible V and would vanish. Thus every column has a zero. Choosing one zero per column gives distinct rows by the at-most-one-zero row bound; with three columns and three rows, the zeros form a permutation. Each row and each column consequently has exactly one zero.")),
                    Paragraph(Text("Fix j. If C₁ⱼ≠0 then σⱼv₁=0. If C₁ⱼ=0, uniqueness of the column's zero gives C₀ⱼ≠0 and σⱼv₀=0; Hermitian symmetry then gives v₀†σⱼ=0. In either case (V†σⱼV)₀₁=0. The coefficient relation gives (V†ρₖV)₀₁=0 for every k. Summing over k and using ∑ₖρₖ=I yields v₀†v₁=(V†V)₀₁=0. But v₀†v₁=0·3+1·0+3·1=3≠0, a contradiction. This rules out the weak factorization for this unital qutrit channel without imposing normalization or invertibility on the filters."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("marquez-gonzalez-2026-positive-filter-transpose-refutation"), ResolutionKind.Refuted))),
        []));

    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. xs]);
    private static Formula At(Formula x, params Formula[] xs) => new Formula.Apply(x, [.. xs]);
    private static Formula All(string v, Formula type, Formula body) => Seq(Forall, Sp, F.Id(v), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string v, Formula type, Formula body) => Seq(Exists, Sp, F.Id(v), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula And(Formula x, Formula y) => Seq(Parenthesized(x), Sp, Land, Sp, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => Seq(Parenthesized(x), Sp, Implies, Sp, Parenthesized(y));
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Fin3 => Call("Fin", D(3));
    private static Formula Mat => Call("Matrix", Fin3, Fin3, Seq(Mathbb, Grp(F.Id("C"))));
    private static Formula Map => Call("MatrixMap", Fin3, Fin3, Seq(Mathbb, Grp(F.Id("C"))));

    private static Formula ClaimFormula()
    {
        Formula f = F.Id("F"), s = F.Id("S"), k = F.Id("K"), p = F.Id("P"), e = F.Id("E");
        Formula transposed = TransposedFamily(s, k);
        Formula factor = And(Call("IsPositive", p), And(Call("IsCompletelyPositive", e),
            Eqn(Call("ofKraus", transposed, transposed), Compose(p, f, e))));
        Formula quantified = All("S", F.Id("Type"),
            Seq(OpenBracket, Call("Fintype", s), CloseBracket, Sp,
                All("K", new Formula.TypeArrow(s, Mat), Imp(Eqn(f, Call("ofKraus", k, k)),
                    Ex("P", Map, Ex("E", Map, factor))))));
        return Seq(F.Id("claim"), Sp, Iff, Sp,
            Parenthesized(All("F", Map, Imp(Call("UnitalChannel", f), quantified))));
    }

    private static Formula TransposeFormula()
    {
        Formula s = F.Id("S"), k = F.Id("K"), x = F.Id("X"), i = F.Id("i");
        Formula transposed = TransposedFamily(s, k);
        Formula rhs = SumOver("i", s, Mul(Mul(Call("transpose", At(k, i)), x),
            Call("conjTranspose", Call("transpose", At(k, i)))));
        return All("S", F.Id("Type"),
            Seq(OpenBracket, Call("Fintype", s), CloseBracket, Sp,
                All("K", new Formula.TypeArrow(s, Mat), And(All("X", Mat,
                    Eqn(At(Call("ofKraus", transposed, transposed), x), rhs)),
                    All("i", s, Eqn(Call("conjTranspose", Call("transpose", At(k, i))),
                        Call("map", At(k, i), F.Id("star"))))))));
    }

    private static Formula SumOver(string v, Formula indexType, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(v), Sp, Colon, Sp, indexType), Sp, Parenthesized(body));
    private static Formula Compose(Formula left, Formula middle, Formula right) =>
        Seq(left, Sp, Circ, Sp, middle, Sp, Circ, Sp, right);
    private static Formula TransposedFamily(Formula indexType, Formula family) =>
        Parenthesized(Seq(LambdaLower, Sp, F.Id("i"), Sp, Colon, Sp, indexType,
            Comma, Sp, Call("transpose", At(family, F.Id("i")))));

    private static Formula PhyslibCall(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula PhyslibAll(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula PhyslibImp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula PhyslibAnd(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula PhyslibEqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula PhyslibMul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula PhyslibMat(string n, string r) => PhyslibCall("Matrix", F.Id(n), F.Id(n), F.Id(r));
    private static Formula PhyslibMap(string a, string b, string r) => PhyslibCall("MatrixMap", F.Id(a), F.Id(b), F.Id(r));
    private static Formula PhyslibTrace(Formula x) => PhyslibCall("tr", x);
    private static Formula PhyslibDual(Formula x) => PhyslibCall("dual", x);
    private static Formula PhyslibApply(Formula f, Formula x) => new Formula.Apply(f, [x]);

    private static Formula PhyslibHermitianDefinition() => Seq(
        PhyslibCall("IsHermitianPreserving", F.Id("M")), Sp, Iff, Sp,
        PhyslibAll("X", PhyslibMat("A", "R"), PhyslibImp(PhyslibCall("IsHermitian", F.Id("X")),
            PhyslibCall("IsHermitian", PhyslibApply(F.Id("M"), F.Id("X"))))));

    private static Formula PhyslibDualDefinition() => PhyslibEqn(PhyslibDual(F.Id("M")),
        Seq(F.Id("tauA"), Sp, Circ, Sp, PhyslibCall("inverse", F.Id("betaA")), Sp, Circ, Sp,
            F.Id("Mvee"), Sp, Circ, Sp, F.Id("betaB"), Sp, Circ, Sp, F.Id("tauB")));

    private static Formula PhyslibTraceEquality() => PhyslibAll("M", PhyslibMap("A", "B", "R"),
        PhyslibAll("X", PhyslibMat("A", "R"), PhyslibAll("Y", PhyslibMat("B", "R"),
            PhyslibEqn(PhyslibTrace(PhyslibMul(PhyslibApply(F.Id("M"), F.Id("X")), F.Id("Y"))),
                PhyslibTrace(PhyslibMul(F.Id("X"), PhyslibApply(PhyslibDual(F.Id("M")), F.Id("Y"))))))));

    private static Formula PhyslibDualPreservation(string property) => PhyslibAll("M", PhyslibMap("A", "B", "complex"),
        PhyslibImp(PhyslibCall(property, F.Id("M")), PhyslibCall(property, PhyslibDual(F.Id("M")))));

    private static Formula PhyslibKernelSum() => PhyslibAll("f", new Formula.TypeArrow(F.Id("I"), PhyslibCall("HermitianMatrix", F.Id("n"), F.Id("R"))),
        PhyslibImp(PhyslibAll("i", F.Id("I"), new Formula.Relation(Num(0), FormulaRelationOperator.LessThanOrEqual,
                PhyslibApply(F.Id("f"), F.Id("i")))),
            PhyslibEqn(PhyslibCall("ker", Seq(Sum, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("I")), Sp,
                    PhyslibApply(F.Id("f"), F.Id("i")))),
                PhyslibCall("intersection", F.Id("I"), PhyslibCall("kernels", F.Id("f"))))));

    private static Formula PhyslibTraceNonnegative() => PhyslibAll("X", PhyslibMat("n", "R"),
        PhyslibAll("Y", PhyslibMat("n", "R"), PhyslibImp(PhyslibAnd(PhyslibCall("PosSemidef", F.Id("X")),
            PhyslibCall("PosSemidef", F.Id("Y"))),
            new Formula.Relation(Num(0), FormulaRelationOperator.LessThanOrEqual,
                PhyslibTrace(PhyslibMul(F.Id("X"), F.Id("Y")))))));
}
