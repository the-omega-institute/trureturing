using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators.ReproducingKernels;

internal sealed class CompletePseudoPickQuotientRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/HilbertOperators/ReproducingKernels/CompletePseudoPickQuotientRefutation";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/HilbertOperators/luomcculloughtsikalas2026beurling");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-point complete pseudo-Pick pair has a quotient with a negative quadratic form.",
        H("Complete pseudo-Pick does not imply quotient positivity"),
        Blocks(
            Definition("pick-matrix", "pickMatrix", "The source block Pick matrix", PickFormula(),
                "Definition 9.2, page 45, uses the condition “(I − WᵢWⱼ*)k(zᵢ, zⱼ) ⪰ 0”. "
                + "The displayed matrix contains all n by n blocks, each of size m by m, with indices in Fin n × Fin m. "
                + "The letter m replaces the source's matrix-size letter k; k remains the scalar kernel. Matrix.conjTranspose is the matrix adjoint."),
            Definition("multiplier", "IsContractiveMultiplier", "Contractivity on the target space", MultiplierFormula(),
                "Section 3, page 15, states: “In this case, Φ induces a bounded operator MΦ : Hκ ⊗ F → Hλ ⊗ E whose norm is the smallest C ≥ 0 such that "
                + "X × X ∋ (a,b) ↦ C²λ(a,b)I_E − Φ(a)Φ(b)* κ(a,b) is positive semi-definite.” "
                + "Here C = 1, κ = λ = ell, and E = F = ℂᵐ. Matrix.PosSemidef tests Hermitian symmetry and nonnegative quadratic forms on all finitely supported vectors."),
            Definition("complete-pseudo-pick", "CompletePseudoPick", "Complete pseudo-Pick pairs", CompleteFormula(),
                "Definition 9.2, page 45: “A pair (k, ℓ) on a set X is a complete pseudo-Pick pair if, whenever positive integer n and k, "
                + "points z₁, …, zₙ ∈ X and matrices W₁, …, Wₙ ∈ Mₖ(ℂ) satisfy (I − WᵢWⱼ*)k(zᵢ, zⱼ) ⪰ 0, "
                + "there exists a contractive multiplier Φ ∈ Mult(Hℓ ⊗ ℂᵏ, Hℓ ⊗ ℂᵏ) such that Φ(zᵢ)=Wᵢ for all i.” "
                + "Both positive sizes are arbitrary. The list z may repeat points. The interpolating function is defined on all of X and acts on the target space in both domain and codomain."),
            Definition("claim", "claim", "Question 9.3", Iff(Local("claim"), ClaimBody()),
                "Question 9.3, page 45: “Let (k, ℓ) be a pair of reproducing kernels with k non-vanishing. If (k, ℓ) is complete pseudo-Pick, do we have ℓ/k ⪰ 0?” "
                + "The affirmative assertion ranges over every X : Type and two complex kernels. Non-vanishing means k x y ≠ 0 for every pair x,y, so the quotient uses no zero denominator. "
                + "The notation ell denotes ℓ. No assumption of strict positive definiteness, holomorphicity or distinct interpolation nodes is imposed."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("A three-point counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("On Fin 3 take coordinates (1/10,1,2), source kernel k(i,j)=1+xᵢxⱼ, and target kernel ell(i,j)=1+δᵢⱼxᵢ². "
                        + "Both kernels are positive semidefinite, and every source entry is nonzero. The quotient has diagonal entries one and off-diagonal entries 10/11, 5/6 and 1/3. "
                        + "Its quadratic form at (−2,1,1) is −10/33.")),
                    Paragraph(Text("Source Pick positivity forces equal matrices at repeated points. When all three points occur, the two relations with coefficients "
                        + "(−1,19/10,−9/10) and their coordinate-weighted values force all three matrices to agree. A constant contractive multiplier then interpolates the data.")),
                    Paragraph(Text("For two observed points, copy one value to the omitted point. Three rational diagonal factorizations certify positivity of the corresponding scalar quotient matrices; "
                        + "the Schur product theorem gives a contractive multiplier on the whole three-point set. Single-point data have a constant extension. "
                        + "These cases cover every finite node list and every positive matrix size.")),
                    Paragraph(Text("The three source kernel vectors are dependent. Thus complete pseudo-Pick interpolation does not detect this three-point quotient obstruction. "
                        + "The infinite-rank family, a strictly positive-definite source, holomorphic kernels, and the separate implication to BLH are not asserted here."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("op-lmt2607q93"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string id, string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula PickFormula()
    {
        Formula x = X("X");
        Formula n = X("n");
        Formula m = X("m");
        Formula p = X("p");
        Formula q = X("q");
        Formula z = X("z");
        Formula w = X("W");
        Formula indices = Product(FinOf(n), FinOf(m));
        Formula body = Lambda("p", indices, Lambda("q", indices,
            Mul(At(Sub(D(1), Mul(At(w, Proj(p, 1)), Adjoint(At(w, Proj(q, 1))))), Proj(p, 2), Proj(q, 2)),
                At(X("k"), At(z, Proj(p, 1)), At(z, Proj(q, 1))))));
        return All("X", Q("Type"), All("k", MatrixType(x), All("n", Naturals(), All("m", Naturals(),
            All("z", Arrow(FinOf(n), x), All("W", Arrow(FinOf(n), MatrixType(FinOf(m))),
                Equal(LCall("pickMatrix", X("k"), z, w), body)))))));
    }

    private static Formula MultiplierFormula()
    {
        Formula x = X("X");
        Formula m = X("m");
        Formula phi = X("Phi");
        Formula p = X("p");
        Formula q = X("q");
        Formula indices = Product(x, FinOf(m));
        Formula body = Lambda("p", indices, Lambda("q", indices,
            Mul(At(Sub(D(1), Mul(At(phi, Proj(p, 1)), Adjoint(At(phi, Proj(q, 1))))), Proj(p, 2), Proj(q, 2)),
                At(X("ell"), Proj(p, 1), Proj(q, 1)))));
        return All("X", Q("Type"), All("ell", MatrixType(x), All("m", Naturals(),
            All("Phi", Arrow(x, MatrixType(FinOf(m))),
                Iff(LCall("IsContractiveMultiplier", X("ell"), m, phi), Positive(body))))));
    }

    private static Formula CompleteFormula() =>
        All("X", Q("Type"), All("k", MatrixType(X("X")), All("ell", MatrixType(X("X")),
            Iff(LCall("CompletePseudoPick", X("k"), X("ell")), CompleteBody()))));

    private static Formula CompleteBody()
    {
        Formula x = X("X");
        Formula n = X("n");
        Formula m = X("m");
        Formula z = X("z");
        Formula w = X("W");
        Formula phi = X("Phi");
        Formula values = All("i", FinOf(n), Equal(At(phi, At(z, X("i"))), At(w, X("i"))));
        Formula extension = Some("Phi", Arrow(x, MatrixType(FinOf(m))),
            And(LCall("IsContractiveMultiplier", X("ell"), m, phi), values));
        Formula datum = All("z", Arrow(FinOf(n), x), All("W", Arrow(FinOf(n), MatrixType(FinOf(m))),
            Implies(Positive(LCall("pickMatrix", X("k"), z, w)), extension)));
        return All("n", Naturals(), Implies(Less(D(0), n),
            All("m", Naturals(), Implies(Less(D(0), m), datum))));
    }

    private static Formula ClaimBody()
    {
        Formula x = X("X");
        Formula k = X("k");
        Formula ell = X("ell");
        Formula quotient = Lambda("x", x, Lambda("y", x,
            new Formula.Fraction(At(ell, X("x"), X("y")), At(k, X("x"), X("y")))));
        Formula nonzero = All("x", x, All("y", x, NotEqual(At(k, X("x"), X("y")), D(0))));
        return All("X", Q("Type"), All("k", MatrixType(x), All("ell", MatrixType(x),
            Implies(Positive(k), Implies(Positive(ell), Implies(nonzero,
                Implies(LCall("CompletePseudoPick", k, ell), Positive(quotient))))))));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Local(string name) => Q(name);
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
    private static Formula Typed(string name, Formula type) => Parenthesized(Seq(X(name), Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(Q("fun"), Sp, Typed(name, type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Product(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula FinOf(Formula n) => At(Q("Fin"), n);
    private static Formula MatrixType(Formula index) => At(Q("Matrix"), index, index, Complexes());
    private static Formula Proj(Formula value, int component) => Seq(Parenthesized(value), Dot, Num(component));
    private static Formula Adjoint(Formula value) => At(Q("Matrix", "conjTranspose"), value);
    private static Formula Positive(Formula value) => At(Q("Matrix", "PosSemidef"), value);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
}
