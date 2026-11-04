using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class ZhangJingPowerCaseSettlementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/zhangjing2025positive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The power block characterizes normality for 1/2 ≤ a < 1, including singular matrices; "
            + "at a = 1 it is positive semidefinite for every matrix.",
        H("The sharp upper endpoint of the Zhang–Jing power block"), Blocks(
            Entry("closed-interval", "claim", "The source's unresolved closed interval",
                Disp(Iff(V("claim"), Parenthesized(ClaimBody(false)))),
                "After Remark 2.13, p. 601: “Due to the limitations of our research method, we cannot "
                + "solve the problem that Theorem 2.3 holds for 1/2 ≤ a ≤ 1.” The proposition expands "
                + "the equivalence over every real a in that interval, every natural dimension n, "
                + "and every complex square matrix A. The matrix functions use Real.rpow, with x⁰ = 1. "
                + "PosSemidef means positive semidefinite, and normality means Aᴴ A = A Aᴴ.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("endpoint-refutation", "result", "The extension to a = 1 fails",
                Disp(Seq(Neg, Sp, Parenthesized(ClaimBody(false)))),
                "At a = 1 the diagonal corners are Aᴴ A and I, so the block is Qᴴ Q for Q = [A,I], "
                + "padded by zero rows to form a square matrix. It is positive semidefinite for every A. "
                + "For A = [[0,1],[2,0]], the (0,0) entries of Aᴴ A and A Aᴴ are 4 and 1. Thus A is "
                + "nonnormal and the universal equivalence on the closed interval is false.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            new DocumentBlock.Section(H("Application below the upper endpoint"), Blocks(
                new DocumentBlock.DisplayFormula(ClaimBody(true)),
                Paragraph(Text("The strict interval is a substantive application of existing results, with the following literal scope. The parameter a is any real number with both guards, n is any natural number including zero, and A is any complex square matrix, including singular matrices. There is no Nonempty, invertibility, positive singular-value, commutativity or additional continuity assumption. Put f(x) = Real.rpow x (2a) and g(x) = Real.rpow x (2(1−a)). The canonical ZhangJingBlockNormalityRefutation.block is exactly Matrix.fromBlocks (cfc f (CFC.sqrt (Aᴴ A))) Aᴴ A (cfc g (CFC.sqrt (Aᴴ A))); normality is the displayed equality.")),
                Paragraph(Text("Use D5.S3.Quantum.Foundation.FiniteTraceDistance.exists_svd_sqrt_eigenvalues on this same A. With dᵢ = Real.sqrt(eigenvalues(Aᴴ A)ᵢ), dᵢ ≥ 0, D = diag(dᵢ), it supplies unitary V,W and A = V D Wᴴ. Unitary cancellation gives Aᴴ A = W D² Wᴴ and A Aᴴ = V D² Vᴴ. CFC.sqrt_eq_real_sqrt, cfcₙ_eq_cfc with Real.sqrt_zero, the canonical D5.S3.Quantum.Information.RenyiInformationCombiningOrderThree.cfc_unitary_diagonal, and Real.sqrt_sq give |A| = W D Wᴴ. The SVD supplier requires only Fintype and DecidableEq on Fin n, with no nonzero dimension or rank restriction. Its physlib-source attribution and Apache-2.0 license remain those of its canonical owner.")),
                Paragraph(Text("Set U = Wᴴ V, F = diag(dᵢ^(2a)), G = diag(dᵢ^(2(1−a))) and T = diag(W,V). T is unitary. Applying the same canonical CFC transport to f and g on the same d gives Tᴴ block(f,g,A) T = [[F,D],[D,Uᴴ G U]]. Matrix.IsUnit.posSemidef_star_left_conjugate_iff therefore identifies positivity of the original block with positivity of this coordinate block. These are two functions of one actual singular-value realization, not independently selected spectra.")),
                Paragraph(Text("For the forward direction put P = diag(dᵢ^(1−2a)). Entrywise PF = D and PD = G. For dᵢ > 0 these follow from Real.rpow_add. For dᵢ = 0 the factors dᵢ^(2a) and dᵢ^(2(1−a)) vanish because both exponents are positive. At a = 1/2, P has 0^0 = 1 on the zero fiber, and both products still vanish; for a > 1/2, Real.zero_rpow at the nonzero negative exponent gives Pᵢᵢ = 0 there. Thus no inverse of F or invertible Schur complement is required.")),
                Paragraph(Text("Let L = [[−P,0],[I,0]]. Matrix.PosSemidef.conjTranspose_mul_mul_same and direct block multiplication yield Lᴴ [[F,D],[D,Uᴴ G U]] L = diag(Uᴴ G U−G,0). Matrix.PosSemidef.submatrix gives Uᴴ G U−G positive semidefinite. Matrix.trace_units_conj' makes its trace zero; Matrix.PosSemidef.trace_eq_zero_iff makes it zero. By commute_unitary_iff_star_left_conjugate, U G = G U. At each entry with Uᵢⱼ ≠ 0 cancel that scalar, then apply Real.rpow_left_inj to the nonnegative dᵢ,dⱼ with exponent 2(1−a) ≠ 0. Entries with Uᵢⱼ = 0 vanish directly. Hence U D = D U. The same entrywise argument with exponent 2, together with the two Gram identities above and unitary cancellation, equates U D = D U with Aᴴ A = A Aᴴ. This proves positivity implies normality.")),
                Paragraph(Text("For the reverse direction, normality and the Gram identities give commutation with D², and exponent-2 injectivity gives U D = D U. Commute.cfc_real applied to g, with D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal, gives Uᴴ G U = G. Set X = diag(dᵢ^a), Y = diag(dᵢ^(1−a)). Real.rpow_add' applies also at zero because the sums 2a, 2(1−a), and 1 are nonzero: X² = F, Y² = G, XY = YX = D. Thus [[F,D],[D,G]] is Qᴴ Q for the padded row Q = [X,Y], and Matrix.posSemidef_conjTranspose_mul_self makes it positive semidefinite. Unitary transport returns the original block's positivity. This proves normality implies positivity.")),
                Paragraph(Text("Every construction also applies to Fin 0: the matrix and index equalities are empty and no choice of an index or positive rank is used. The half endpoint and zero singular values are included in both directions. At a = 1, g is constant and the injectivity step fails exactly as in the retained refutation. The published lower interval 0 ≤ a ≤ 1/2 is literature-attested Theorem 2.3, not independently formalized here. Parameters outside [0,1], infinite-dimensional operators, a general functional injectivity repair and a new singular-matrix classification are outside this application. The earlier Question 2.14 scalar-pair refutation is distinct.")),
                Paragraph(Text("The application introduces no retained positive theorem, GID, resolution marker or audit wrapper. The canonical CFC supplier's dependent/pointwise arena, exact reconstruction, whole-family intervention and sensitivity audit remains unfinished; removing an application declaration does not finish that audit. Literature completeness and priority remain ASSUMED-UNVERIFIED.")))))));


    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("zhang-jing-2025-block-criterion-power-case-theorem-2-3"),
                ResolutionKind.Refuted) : null);

    private static Formula ClaimBody(bool belowOne)
    {
        Formula a = V("a"), n = V("n"), matrix = V("A"), x = V("x");
        Formula first = Fun("x", Real(), new Formula.Power(x, Mul(D(2), a)));
        Formula second = Fun("x", Real(), new Formula.Power(x,
            Mul(D(2), Parenthesized(Sub(D(1), a)))));
        Formula equivalence = Iff(Call("Matrix.PosSemidef", Call("D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation.block", first, second, matrix)),
            Equal(Mul(Conj(matrix), matrix), Mul(matrix, Conj(matrix))));
        Formula upper = belowOne ? Lt(a, D(1)) : Leq(a, D(1));
        return All("a", Real(), Imp(Leq(new Formula.Fraction(D(1), D(2)), a),
            Imp(upper, All("n", Nat(), All("A", MatrixType(n), equivalence)))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
    private static Formula MatrixType(Formula n) => Call("Matrix", Call("Fin", n), Call("Fin", n), Complex());
    private static Formula Conj(Formula a) => Call("Matrix.conjTranspose", a);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(
        Seq(Operatorname, Grp(Seq(name.Split('.').Select((part, index) =>
            index == 0 ? V(part) : Seq(Dot, V(part))).ToArray()))), args);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Fun(string name, Formula type, Formula body) =>
        Parenthesized(Seq(V("fun"), Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
}
