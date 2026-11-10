using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators;

internal sealed class LarotondaReyNormingFlatnessRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/HilbertOperators/LarotondaReyNormingFlatnessRefutation";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/HilbertOperators/larotonda2023weaklyinvariant");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Central norming matrices coexist with strict norm increase on every nonzero commutator-line step.",
        H("Norming commutation does not imply local commutator-line flatness"),
        Blocks(
            Definition("pairing", "pairing", "Real trace duality", PairingFormula(),
                AssessedProvenance.FromLiterature(Source),
                "On page 4, the trace-duality remark states: “We say that φ ∈ 𝔲ₙ′ is a unit norming functional of V ∈ 𝔲ₙ if φ(V) = ‖V‖ and ‖φ‖ = 1.” "
                    + "The real part of −Matrix.trace (N * Y) gives that real pairing on skew-adjoint matrices."),
            Definition("finsler", "IsAdInvariantFinsler", "The Ad-invariant Finsler class", FinslerFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Definition 2.1 on page 3 says: “It is a function ‖·‖ : 𝔲ₙ → ℝ≥0 such that for any X,Y ∈ 𝔲ₙ” and specifies “‖X‖ = 0 if and only if X = 0 (non-degenerate)”, "
                    + "“‖X+Y‖ ≤ ‖X‖+‖Y‖ (subadditive)”, “‖λX‖ = λ‖X‖ for any λ ∈ ℝ≥0 (positively homogenous)” and “‖UXU*‖ = ‖X‖ for any U ∈ 𝐔(n,ℂ) (Ad-invariant).” "
                    + "Here F is an ambient matrix function, with the four conditions imposed on skewAdjoint. Nonnegativity and F 0 = 0 are explicit."),
            Definition("dual-norm", "dualNorm", "The dual supremum", DualFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The trace-duality remark on page 4 defines ‖φ‖ = max{φ(X): ‖X‖ ≤ 1}, without the modulus. "
                    + "dualNorm uses sSup on the real trace-pairing values of the skew-adjoint unit ball."),
            Definition("norming", "IsNorming", "Unit norming matrices", NormingFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The same remark states: “We say that φ ∈ 𝔲ₙ′ is a unit norming functional of V ∈ 𝔲ₙ if φ(V) = ‖V‖ and ‖φ‖ = 1.” "
                    + "N is required to be skew-adjoint, have dualNorm one and attain F V under pairing."),
            Definition("spectral-data", "SpectralData", "Finite spectral blocks", SpectralFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Definition 2.30 on page 14 states: “Let 0 ≠ V ∈ 𝔲ₙ, write V = i Σₖ∈F vₖPₖ with v₁ > v₂ > ⋯ > v_F a diagonalization of V where the eigenvalues are different and ordered decreasingly. "
                    + "Each Pₖ is an orthonormal projection onto the corresponding eigenspace and PₖPⱼ = 0 for k ≠ j.” "
                    + "SpectralData stores a positive number of blocks, their real values and nonzero self-adjoint idempotent projections, orthogonality, completeness, the decomposition and skew-adjointness. "
                    + "Distinct values replace the source's decreasing enumeration; summation and codiagonal are invariant under a permutation of blocks. "
                    + "Each row below gives one field with its full dependent type."),
            Definition("codiagonal", "codiagonal", "The codiagonal part", CodiagonalFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Definition 2.30 on page 14 states “X_D = Σₖ PₖXPₖ and X_C = Σₖ≠ⱼ PₖXPⱼ”, the block-diagonal and block-codiagonal parts of X. "
                    + "The double finite sum retains precisely the unequal eigenvalue blocks."),
            Definition("claim", "claim", "Problem 3.13", Equivalence(Local("claim"), ClaimBody()),
                AssessedProvenance.FromLiterature(Source),
                "Problem 3.13, page 26: “Does [N,X_C] = 0 for all N norming V imply that ‖V+s[X,V]‖ = ‖V‖ in some interval |s| < δ?” "
                    + "The assertion ranges over positive natural dimensions, ambient real-valued matrix functions in the displayed Finsler class, skew-adjoint V and X, and every SpectralData decomposition of V. "
                    + "It includes existence of a norming matrix and a spectral decomposition. The matrices use Fin n indices starting at zero; [X,V] is X * V − V * X."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("A two-dimensional counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The polar supremum is taken over 0 ≤ q ≤ 1 of ((1−q²)|tr(Y)/2| + 2q‖Y−(tr(Y)/2)I‖)/(1+q²+q). "
                        + "The matrix norm in this expression is the Euclidean operator norm, supplied by Matrix.Norms.L2Operator. "
                        + "The proof establishes nondegeneracy, the triangle inequality, absolute real homogeneity and unitary conjugation invariance.")),
                    Paragraph(Text("Take V = diag(3i/2,i/2) and X = [[0,1],[−1,0]]. The norm of V is one. "
                        + "For any traceless skew-adjoint W the norm at V+eW is at most 1+e²‖W‖². "
                        + "Consequently each norming functional at V annihilates every traceless skew direction, so its representing matrix is central and commutes with every codiagonal part.")),
                    Paragraph(Text("Along V+s[X,V] the central coordinate stays i, while the squared operator norm of the traceless part is 1/4+s². "
                        + "Every nonzero s therefore strictly increases the polar supremum. Choosing s = δ/2 contradicts any positive local flatness radius.")),
                    Paragraph(Text("This is a counterexample in dimension two. Identification of this polar supremum with the compact-body gauge, a normalized rank-one formulation and the family in every higher dimension are not established by this theorem. "
                        + "Theorem 3.11 asks for a norming functional at the endpoint V+[X,V], which is a different condition. "
                        + "The exact-arithmetic gauge experiment is in the-omega-institute/trureturing-experiments, commit 87e62bfeeb39619d3a1bfb1c04a82ad22c66c535, "
                        + "docs/reports/larotonda-rey-2023-problem-3-13-norming-commutation-flatness. Its command is python3 check.py, reported exit 0; "
                        + "check.py has SHA-256 f7feab60bc4bf9d55c5e29519c0b61eb0c57fe13222bd476cc8069ab8d33775d. "
                        + "Those calculations concern the gauge; they supply no additional theorem identifying it with the polar supremum."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("larotonda-rey-problem-3-13"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static Formula PairingFormula() => All("n", Naturals(), All("N", MatrixType(X("n")),
        All("Y", MatrixType(X("n")), Equal(LCall("pairing", X("N"), X("Y")),
            Seq(Minus, Parenthesized(At(Q("Complex", "re"), At(Q("Matrix", "trace"), Mul(X("N"), X("Y"))))))))));

    private static Formula FinslerFormula()
    {
        Formula n = X("n");
        Formula f = X("F");
        Formula y = X("Y");
        Formula z = X("Z");
        Formula u = X("U");
        Formula r = X("r");
        Formula body = And(Equal(At(f, D(0)), D(0)),
            All("Y", MatrixType(n), Implies(Skew(y, n), Leq(D(0), At(f, y)))),
            All("Y", MatrixType(n), Implies(Skew(y, n), Equivalence(Equal(At(f, y), D(0)), Equal(y, D(0))))),
            All("Y", MatrixType(n), All("Z", MatrixType(n), Implies(Skew(y, n), Implies(Skew(z, n),
                Leq(At(f, Add(y, z)), Add(At(f, y), At(f, z))))))),
            All("r", Reals(), All("Y", MatrixType(n), Implies(Leq(D(0), r), Implies(Skew(y, n),
                Equal(At(f, Smul(r, y)), Mul(r, At(f, y))))))),
            All("U", MatrixType(n), All("Y", MatrixType(n), Implies(Member(u, At(Q("Matrix", "unitaryGroup"), FinOf(n), Complexes())),
                Implies(Skew(y, n), Equal(At(f, Mul(Mul(u, y), At(Q("star"), u))), At(f, y)))))));
        return All("n", Naturals(), All("F", FunctionType(MatrixType(n), Reals()),
            Equivalence(LCall("IsAdInvariantFinsler", f), body)));
    }

    private static Formula DualFormula()
    {
        Formula body = Some("Y", MatrixType(X("n")), And(Skew(X("Y"), X("n")),
            Leq(At(X("F"), X("Y")), D(1)), Equal(X("r"), LCall("pairing", X("N"), X("Y")))));
        Formula set = Seq(Left, OpenBrace, Typed(X("r"), Reals()), Sp, Mid, Sp, body, Right, CloseBrace);
        return All("n", Naturals(), All("F", FunctionType(MatrixType(X("n")), Reals()),
            All("N", MatrixType(X("n")), Equal(LCall("dualNorm", X("F"), X("N")), At(Q("sSup"), set)))));
    }

    private static Formula NormingFormula() => All("n", Naturals(),
        All("F", FunctionType(MatrixType(X("n")), Reals()), All("V", MatrixType(X("n")),
            All("N", MatrixType(X("n")), Equivalence(LCall("IsNorming", X("F"), X("V"), X("N")),
                And(Skew(X("N"), X("n")), Equal(LCall("dualNorm", X("F"), X("N")), D(1)),
                    Equal(LCall("pairing", X("N"), X("V")), At(X("F"), X("V")))))))));

    private static Formula SpectralFormula()
    {
        Formula n = X("n");
        Formula d = X("D");
        Formula b = Field("blocks");
        Formula v = Field("value");
        Formula p = Field("projection");
        Formula i = X("i");
        Formula j = X("j");
        Formula pi = At(p, i);
        Formula pj = At(p, j);
        Formula[] rows = [
            Typed(d, LCall("SpectralData", n)),
            Typed(b, Naturals()),
            Typed(Field("positiveBlocks"), Less(D(0), b)),
            Typed(v, FunctionType(FinOf(b), Reals())),
            Typed(p, FunctionType(FinOf(b), MatrixType(n))),
            Typed(Field("V"), MatrixType(n)),
            Typed(Field("distinct"), All("i", FinOf(b), All("j", FinOf(b),
                Implies(NotEqual(i, j), NotEqual(At(v, i), At(v, j)))))),
            Typed(Field("selfAdjointProjection"), All("i", FinOf(b), Equal(At(Q("star"), pi), pi))),
            Typed(Field("idempotentProjection"), All("i", FinOf(b), Equal(Mul(pi, pi), pi))),
            Typed(Field("orthogonalProjection"), All("i", FinOf(b), All("j", FinOf(b),
                Implies(NotEqual(i, j), Equal(Mul(pi, pj), D(0)))))),
            Typed(Field("nonzeroProjection"), All("i", FinOf(b), NotEqual(pi, D(0)))),
            Typed(Field("completeProjection"), Equal(SumOver("i", FinOf(b), pi), D(1))),
            Typed(Field("decomposition"), Equal(Field("V"), Smul(Typed(Q("Complex", "I"), Complexes()),
                SumOver("i", FinOf(b), Smul(Typed(At(v, i), Complexes()), pi))))),
            Typed(Field("skewV"), Skew(Field("V"), n))
        ];
        return new Formula.Aligned([.. rows.Select(row => All("n", Naturals(), All("D", LCall("SpectralData", n), row)))]);
    }

    private static Formula CodiagonalFormula()
    {
        Formula d = X("D");
        Formula j = X("j");
        Formula k = X("k");
        Formula value = At(Q("SpectralData", "value"), d);
        Formula projection = At(Q("SpectralData", "projection"), d);
        Formula body = SumOver("j", FinOf(At(Q("SpectralData", "blocks"), d)),
            SumOver("k", FinOf(At(Q("SpectralData", "blocks"), d)),
                Seq(Q("if"), Sp, Parenthesized(NotEqual(At(value, j), At(value, k))), Sp, Q("then"), Sp,
                    Parenthesized(Mul(Mul(At(projection, j), X("X")), At(projection, k))), Sp, Q("else"), Sp, D(0))));
        return All("n", Naturals(), All("D", LCall("SpectralData", X("n")), All("X", MatrixType(X("n")),
            Equal(LCall("codiagonal", d, X("X")), body))));
    }

    private static Formula ClaimBody()
    {
        Formula n = X("n");
        Formula f = X("F");
        Formula v = X("V");
        Formula d = X("D");
        Formula x = X("X");
        Formula c = LCall("codiagonal", d, x);
        Formula commute = All("N", MatrixType(n), Implies(LCall("IsNorming", f, v, X("N")),
            Equal(Mul(X("N"), c), Mul(c, X("N")))));
        Formula flat = Some("δ", Reals(), And(Less(D(0), X("δ")), All("s", Reals(),
            Implies(Less(new Formula.Absolute(X("s")), X("δ")), Equal(
                At(f, Add(v, Smul(X("s"), Sub(Mul(x, v), Mul(v, x))))), At(f, v))))));
        Formula assertions = And(Some("N", MatrixType(n), LCall("IsNorming", f, v, X("N"))),
            Some("D", LCall("SpectralData", n), Equal(At(Q("SpectralData", "V"), d), v)),
            All("D", LCall("SpectralData", n), Implies(Equal(At(Q("SpectralData", "V"), d), v),
                All("X", MatrixType(n), Implies(Skew(x, n), Implies(commute, flat))))));
        return All("n", Naturals(), Implies(Less(D(0), n),
            All("F", FunctionType(MatrixType(n), Reals()), Implies(LCall("IsAdInvariantFinsler", f),
                All("V", MatrixType(n), Implies(Skew(v, n), assertions))))));
    }

    private static Formula Field(string name) => At(Q("SpectralData", name), X("D"));
    private static Formula Skew(Formula value, Formula n) => Member(value, At(Q("skewAdjoint"), MatrixType(n)));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => At(Q("Fin"), n);
    private static Formula MatrixType(Formula n) => At(Q("Matrix"), FinOf(n), FinOf(n), Complexes());
    private static Formula X(string name) => name == "δ" ? DeltaLower : F.Id(name);
    private static Formula Local(string name) => Q("D5", "S3", "HilbertOperators", "LarotondaReyNormingFlatnessRefutation", name);
    private static Formula LCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Q(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula FunctionType(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Equivalence(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(params Formula[] clauses) => clauses.Length == 1 ? clauses[0] :
        new Formula.Logic(Parenthesized(clauses[0]), FormulaLogicOperator.And, Parenthesized(And(clauses.Skip(1).ToArray())));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Smul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
}
