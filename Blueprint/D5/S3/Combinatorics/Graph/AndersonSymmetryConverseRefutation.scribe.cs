using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class AndersonSymmetryConverseRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/lindbladguerrero2025anderson");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A potential on the eight-cycle has an eigenvector with a zero coordinate at every real coupling, while every matrix commuting with its Laplacian and potential is scalar. Thus no orthogonal shared symmetry other than I and -I exists.",
        H("A bad Anderson potential without nontrivial shared symmetry"),
        Blocks(
            Node("nonvanishing", "Non-vanishing eigenvectors", NonvanishingFormula(),
                "nonvanishingEigenvectors",
                "Definition 1.1, page 2: \"We say that V is a good potential if H_t = Δ + tV has simple eigenvalues and non-vanishing eigenvectors for all but finitely many t values.\" Every nonzero complex vector satisfying the eigenvector equation is quantified, and every vertex is required to have a nonzero coordinate. The zero vector is explicitly excluded. The notation *ᵥ is Matrix.mulVec and the scalar action is the usual complex scalar action.",
                AssessedProvenance.FromLiterature(Source)),
            Node("bad", "Bad potentials", BadFormula(), "bad",
                "Definition 1.1, page 2: \"We say that V is a bad potential if H_t fails to satisfy at least one of these conditions for any t ∈ ℝ.\" Here V is Matrix.diagonal v. Section 1, page 2, writes (H_t ψ)(j) = ∑_{k∼j}(ψ(j)−ψ(k)) + t ω_j ψ(j). The graph is Mathlib's SimpleGraph.cycleGraph L, whose adjacency for L > 2 is j−k = 1 or k−j = 1 in Fin L. Its lapMatrix acts by the literal sum of neighbour differences: lapMatrix_mulVec_apply gives degree times the coordinate minus the sum of neighbour coordinates. Both neighbours are distinct for L > 2. The potential and t are coerced from real to complex values in H; every real coupling is quantified. Simple eigenvalues are encoded literally by ∀ μ : ℂ, Polynomial.IsRoot (Matrix.charpoly H) μ → Polynomial.rootMultiplicity μ (Matrix.charpoly H) = 1. Every characteristic-polynomial root is required to have algebraic multiplicity one. Failure of the conjunction is exactly failure of at least one spectral condition.",
                AssessedProvenance.FromLiterature(Source)),
            Node("symmetry", "Nontrivial shared symmetries", SymmetryFormula(), "sharedSymmetry",
                "Section 1, page 2: \"To explain the discrepancy, in section 3 we show shared symmetries — orthogonal matrices that commute with both Δ and V — lead to the failure of our conditions.\" Matrix.orthogonalGroup is the real orthogonal group; membership is equivalent to OᵀO = I. The two scalar symmetries I and −I are excluded from nontriviality. This is the weak converse convention: either sufficient branch of Lemma 3.2, page 7, excludes −I, since (−I)² = I and −Ie_j ≠ e_j. Excluding both scalar matrices makes the question substantive while including every symmetry allowed by those branches.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The Lindblad–Guerrero converse", ClaimFormula(), "claim",
                "After Theorem 1.3, page 3: \"Conversely, we also ask whether every bad potential shares a nontrivial symmetry with the laplacian.\" Section 4, page 8: \"In general, we do not know whether the converse of lemma 3.2 is true.\" The displayed statement is the one-dimensional two-valued instance: every L > 2 and every labelled real potential taking values in {−1,1} is quantified. A counterexample in dimension one refutes the general-grid converse. Any two distinct values are obtained by αV + βI with α ≠ 0; H_t becomes H_{αt} + βtI, which shifts eigenvalues, preserves their multiplicities and preserves eigenvectors. Commutation with the potential is also unchanged by this affine transformation. Thus normalization to {−1,1} covers two-valued distributions.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("lgconv-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The eight-cycle refutation"), StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take v = (1,1,1,1,−1,1,−1,−1). For any real t, put a = √(t²+2)−t. Then a²+2ta−2 = 0, and z = (1,0,−1,a,1−a²,−2t,1,−a) is an eigenvector with eigenvalue 2+a+t = 2+√(t²+2). Its first coordinate is 1 and its coordinate of index 1 is 0, so it is nonzero and violates non-vanishing for every t. To exclude shared symmetries, the finite Laplacian is evaluated exactly. Rational linear combinations of its commutator equations and those of Matrix.diagonal v give O = (O 0 0) • I for every real commuting matrix O. Orthogonality then gives (O 0 0)² = 1, so O is I or −I. The bad potential therefore has no nontrivial shared symmetry."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lindblad-guerrero-2025-anderson-symmetry-converse-refutation"),
                    ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string id, string title, Formula formula, string declaration,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("lgconv-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(Qualified(name))), [.. args]);
    private static Formula Qualified(string name)
    {
        var parts = name.Split('.');
        var tokens = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (tokens.Count != 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq([.. tokens]);
    }
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula ExistsIn(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => Rel(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinL() => Call("Fin", F.Id("L"));
    private static Formula MatrixL(Formula field) => Call("Matrix", FinL(), FinL(), field);
    private static Formula PotentialType() => new Formula.TypeArrow(FinL(), Reals());
    private static Formula Lap(Formula field) => Call("SimpleGraph.lapMatrix", field,
        Call("SimpleGraph.cycleGraph", F.Id("L")));
    private static Formula RealCast(Formula x) => Call("Complex.ofReal", x);
    private static Formula Smul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula MatrixPredicate(string name, Formula rhs) => Disp(All("L", Nats(),
        All("H", MatrixL(Complexes()), Iff(Call(name, F.Id("H")), rhs))));

    private static Formula NonvanishingFormula()
    {
        Formula mu = F.Id("mu"), z = F.Id("z"), j = F.Id("j");
        Formula equation = Eq(Call("Matrix.mulVec", F.Id("H"), z), Smul(mu, z));
        return MatrixPredicate("nonvanishingEigenvectors", All("mu", Complexes(),
            All("z", new Formula.TypeArrow(FinL(), Complexes()), Implies(Ne(z, D(0)),
                Implies(equation, All("j", FinL(), Ne(new Formula.Apply(z, [j]), D(0))))))));
    }
    private static Formula BadFormula()
    {
        Formula t = F.Id("t"), j = F.Id("j"), h = F.Id("H");
        Formula diagonal = Call("Matrix.diagonal", Seq(LambdaLower, Sp,
            Parenthesized(Seq(j, Sp, Colon, Sp, FinL())), Comma, Sp,
            RealCast(new Formula.Apply(F.Id("v"), [j]))));
        Formula hvalue = new Formula.Binary(Lap(Complexes()), FormulaBinaryOperator.Add,
            Smul(RealCast(t), diagonal));
        Formula body = Seq(F.Text, Grp(F.Id("let")), Sp, h, Sp, Colon, Sp, MatrixL(Complexes()),
            Sp, Colon, F.Eq, Sp, hvalue, Semi, Sp,
            new Formula.Not(Parenthesized(And(All("mu", Complexes(), Implies(
                Call("Polynomial.IsRoot", Call("Matrix.charpoly", h), F.Id("mu")),
                Eq(Call("Polynomial.rootMultiplicity", F.Id("mu"), Call("Matrix.charpoly", h)), D(1)))),
                Call("nonvanishingEigenvectors", h)))));
        return Disp(All("L", Nats(), All("v", PotentialType(), Iff(Call("bad", F.Id("v")),
            All("t", Reals(), body)))));
    }
    private static Formula SymmetryFormula()
    {
        Formula o = F.Id("O"), v = F.Id("v"), lap = Lap(Reals());
        Formula diagonal = Call("Matrix.diagonal", v);
        Formula member = Rel(o, FormulaRelationOperator.MemberOf, Call("Matrix.orthogonalGroup", FinL(), Reals()));
        Formula body = And(member, And(Ne(o, D(1)), And(Ne(o, new Formula.Negate(D(1))),
            And(Eq(Mul(o, lap), Mul(lap, o)), Eq(Mul(o, diagonal), Mul(diagonal, o))))));
        return Disp(All("L", Nats(), All("v", PotentialType(), Iff(Call("sharedSymmetry", v),
            ExistsIn("O", MatrixL(Reals()), body)))));
    }
    private static Formula ClaimFormula()
    {
        Formula v = F.Id("v"), j = F.Id("j");
        Formula value = new Formula.Apply(v, [j]);
        Formula binary = All("j", FinL(), Logic(Eq(value, new Formula.Negate(D(1))),
            FormulaLogicOperator.Or, Eq(value, D(1))));
        return Disp(Iff(F.Id("claim"), All("L", Nats(),
            Implies(Rel(D(2), FormulaRelationOperator.LessThan, F.Id("L")),
                All("v", PotentialType(), Implies(binary,
                    Implies(Call("bad", v), Call("sharedSymmetry", v))))))));
    }
}
