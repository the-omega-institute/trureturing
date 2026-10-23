using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class MaximalCoherenceAncillaNonmonotoneDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/baekjonha2026maximalcoherence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Maximal spectral-distance measurement coherence can increase under a CP unital map. The tetrahedral SIC qubit POVM has maximal coherence at most sqrt(2/3)/2, while adjoining an identity qubit gives maximal coherence at least 1/2.",
        H("An identity ancilla defeats maximal measurement coherence monotonicity"),
        Blocks(
            Node("incoherent", "Incoherent measurements", IncoherentFormula(),
                "Section II.A, p. 2: \"In the same spirit, a quantum measurement is called incoherent when all its elements are diagonal in the reference basis:\" The expression following this sentence is A_x = sum_i lambda_{i|x} |i><i|. Matrices have complex entries and outcomes are Fin n. The existing IsPOVM says that every effect is positive semidefinite and that their sum is the identity; IsDiag states diagonality in the reference coordinates.",
                "IsIncoherent", DescribeRole.Definition),
            Node("distance", "The spectral distance", DistanceFormula(),
                "Equation (32), p. 5, at p = infinity is D_infinity(A,B) = (1/2) sum_x norm(A_x - B_x). Section IV.A, p. 7, adopts this distance. The norm is the spectral operator norm on Euclidean space, supplied by Matrix.Norms.L2Operator. This is the contractive distance of Tendick et al., Theorem 5, arXiv:2205.08546.",
                "dInf", DescribeRole.Definition),
            Node("coherence", "Coherence in a fixed basis", CoherenceFormula(),
                "Section II.A, p. 2: \"A natural family of coherence monotones for measurements arises from a distance D between POVMs as\" followed by C_D(A) = min_{B in I(d,n)} D(A,B). The encoding takes sInf of the corresponding set of real distances. The proof establishes nonemptiness and a lower bound for the four-outcome sets it uses.",
                "coh", DescribeRole.Definition),
            Node("maximal", "Maximal coherence over reference bases", MaximalFormula(),
                "Section III.A, p. 4: \"Coherence is intrinsically basis dependent: rotating the reference basis by a unitary U alters the off-diagonal structure of every POVM element. We define the maximal coherence of measurement of 𝖠 as the basis-optimized value of any coherence monotone C_D,\" followed by C_D^max(A) = max_U C_D(U^dagger A U). The encoding takes sSup over Matrix.unitaryGroup, conjugating every effect by the same U. The proof bounds this set above and supplies the identity unitary as a member.",
                "cmax", DescribeRole.Definition),
            Node("dual", "CP unital duals in Kraus form", DualFormula(),
                "In Eq. (12), p. 4, the source's preprocessing map is \"the dual of an arbitrary CPTP quantum preprocessing channel\" between \"(possibly distinct) Hilbert spaces\". Its finite-dimensional encoding uses k rectangular Kraus matrices K_j, with sum_j K_j^dagger K_j = I and Phi(X) = sum_j K_j^dagger X K_j. The dimensions d and e are independent.",
                "IsCPUnitalDual", DescribeRole.Definition),
            Node("claim", "The general monotonicity claim", ClaimFormula(),
                ClaimProse(),
                "claim", DescribeRole.Definition),
            Node("result", "General monotonicity fails", Disp(new Formula.Not(F.Id("claim"))),
                "Take d = 2, e = 4, n = 4, alpha = 1 and q_x = 1/4. The effects are A_i = (I + n_i dot sigma)/4, with tetrahedral vectors (1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1) divided by sqrt(3). The identification of C^2 tensor C^2 with Fin 4 is finProdFinEquiv: (i,j) maps to 2*i+j, ordered |00>, |01>, |10>, |11>. The discarding dual J(X) = X tensor I_2 has two Kraus matrices and is unital. For every qubit unitary, dephasing is an incoherent POVM and the four squared off-diagonal moduli sum to 1/6. Cauchy-Schwarz gives cmax A <= sqrt(2/3)/2. In the Bell basis, every diagonal competitor has scalar normalized partial trace. Applying the Rayleigh bound to a difference and its negative, using eigenvalues 1/2 and 0 of each SIC effect, gives a norm lower bound 1/4 per effect and hence cmax(J(A)) >= 1/2. Since sqrt(2/3)/2 < 1/2, claim is false. This settles the dimension-changing spectral-distance case. The source's dichotomic, mixed-unitary and covariant conclusions retain their hypotheses. Diamond distance and dimension-preserving monotonicity remain open.",
                "result", DescribeRole.Theorem, true,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("baek-jo-nha-2026-maximal-coherence-monotonicity"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula,
        string prose, string declaration, DescribeRole role, bool repositoryResult = false,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("mcancilla-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula),
            repositoryResult ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static DocumentBlock Node(string id, string title, Formula formula,
        BlockSequence prose, string declaration, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("mcancilla-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source), prose, role);

    private static BlockSequence ClaimProse() => Blocks(Paragraph(
        Text("Section III.C, p. 7: \"For non-dichotomic POVMs, the equivalence with sharpness is generally unavailable, and monotonicity must be considered at the channel level: it holds under mixed-unitary channels (Theorem 5) and under unitarily covariant channels (Corollary 6), but whether "),
        Math(In(new Formula.Power(new Formula.Subscript(F.Id("C"), F.Id("D")),
            Seq(Operatorname, Grp(F.Id("max")))))),
        Text(" remains monotonic under general CP unital maps in this regime is left as an open problem.\"")),
        Paragraph(Text(" Table I marks the non-dichotomic row under any fuzzifyng operations as Open. The encoding asks for every outcome count n > 2, every input and output dimension d and e, every POVM A, every CP unital dual Phi, every alpha in [0,1] and every probability distribution q, that the spectral-distance maximal coherence of the fuzzified effects is at most cmax A. The original labels 1,...,n become Fin n; no effect is omitted. Complex scalar casts of alpha and (1-alpha) q_x are explicit.")));

    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, variable, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Apply(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula LeqTo(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Matrix(Formula d, Formula e) =>
        Call("Matrix", Call("Fin", d), Call("Fin", e), Complex());
    private static Formula Family(Formula n, Formula d) => Arrow(Call("Fin", n), Matrix(d, d));
    private static Formula SumOver(Formula x, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(x, Sp, Colon, Sp, type)), Sp, body);
    private static Formula LambdaOver(Formula x, Formula type, Formula body) =>
        Parenthesized(Seq(F.Id("fun"), Sp, x, Sp, Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula SetOf(Formula x, Formula type, Formula predicate) =>
        Seq(OpenBrace, x, Sp, Colon, Sp, type, Sp, Mid, Sp, predicate, CloseBrace);
    private static Formula CastComplex(Formula x) => Parenthesized(Seq(x, Sp, Colon, Sp, Complex()));
    private static Formula Smul(Formula a, Formula b) => Apply(Qualified("SMul", "smul"), a, Parenthesized(b));
    private static Formula Povm(Formula a) => Apply(
        Qualified("D5", "S3", "Quantum", "QuantumChannels", "ConcealmentKernelNecessityRefutation", "IsPOVM"), a);
    private static Formula Conjugated(Formula n, Formula a, Formula u) =>
        LambdaOver(F.Id("x"), Call("Fin", n),
            Multiply(Multiply(Call("star", u), Apply(a, F.Id("x"))), u));

    private static Formula IncoherentFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), b = F.Id("B"), x = F.Id("x");
        return Disp(All(n, Nat(), All(d, Nat(), All(b, Family(n, d),
            Eq(Call("IsIncoherent", b), And(Povm(b),
                All(x, Call("Fin", n), Apply(Qualified("Matrix", "IsDiag"), Parenthesized(Apply(b, x))))))))));
    }
    private static Formula DistanceFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), a = F.Id("A"), b = F.Id("B"), x = F.Id("x");
        Formula norm = Seq(Vert, Sp, Subtract(Apply(a, x), Apply(b, x)), Sp, Vert);
        return Disp(All(n, Nat(), All(d, Nat(), All(a, Family(n, d), All(b, Family(n, d),
            Eq(Call("dInf", a, b), Multiply(new Formula.Fraction(D(1), D(2)),
                SumOver(x, Call("Fin", n), norm))))))));
    }
    private static Formula CoherenceFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), a = F.Id("A"), b = F.Id("B"), r = F.Id("r");
        return Disp(All(n, Nat(), All(d, Nat(), All(a, Family(n, d),
            Eq(Call("coh", a), Call("sInf", SetOf(r, Real(), Some(b, Family(n, d),
                And(Call("IsIncoherent", b), Eq(r, Call("dInf", a, b)))))))))));
    }
    private static Formula MaximalFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), a = F.Id("A"), u = F.Id("U"), r = F.Id("r");
        Formula unitary = Seq(u, Sp, InMacro, Sp,
            Apply(Qualified("Matrix", "unitaryGroup"), Call("Fin", d), Complex()));
        return Disp(All(n, Nat(), All(d, Nat(), All(a, Family(n, d),
            Eq(Call("cmax", a), Call("sSup", SetOf(r, Real(), Some(u, Matrix(d, d),
                And(unitary, Eq(r, Call("coh", Conjugated(n, a, u))))))))))));
    }
    private static Formula DualFormula()
    {
        Formula d = F.Id("d"), e = F.Id("e"), phi = F.Id("Phi"), k = F.Id("k"),
            kraus = F.Id("K"), j = F.Id("j"), x = F.Id("X");
        Formula kj = Apply(kraus, j), adj = Apply(Qualified("Matrix", "conjTranspose"), Parenthesized(kj));
        Formula unital = Eq(SumOver(j, Call("Fin", k), Multiply(adj, kj)), D(1));
        Formula action = All(x, Matrix(d, d), Eq(Apply(phi, x),
            SumOver(j, Call("Fin", k), Multiply(Multiply(adj, x), kj))));
        return Disp(All(d, Nat(), All(e, Nat(), All(phi, Arrow(Matrix(d, d), Matrix(e, e)),
            Eq(Call("IsCPUnitalDual", phi), Some(k, Nat(),
                Some(kraus, Arrow(Call("Fin", k), Matrix(d, e)), And(unital, action))))))));
    }
    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), e = F.Id("e"), n = F.Id("n"), a = F.Id("A"),
            phi = F.Id("Phi"), alpha = F.Id("alpha"), q = F.Id("q"), x = F.Id("x");
        Formula output = LambdaOver(x, Call("Fin", n), Add(
            Smul(CastComplex(alpha), Apply(phi, Parenthesized(Apply(a, x)))),
            Smul(CastComplex(Multiply(Parenthesized(Subtract(D(1), alpha)), Apply(q, x))),
                Parenthesized(Seq(D(1), Sp, Colon, Sp, Matrix(e, e))))));
        Formula body = LeqTo(Call("cmax", output), Call("cmax", a));
        body = Imp(Eq(SumOver(x, Call("Fin", n), Apply(q, x)), D(1)), body);
        body = Imp(All(x, Call("Fin", n), LeqTo(D(0), Apply(q, x))), body);
        body = Imp(LeqTo(alpha, D(1)), body);
        body = Imp(LeqTo(D(0), alpha), body);
        body = Imp(Call("IsCPUnitalDual", phi), body);
        body = Imp(Povm(a), body);
        body = Imp(Rel(D(2), FormulaRelationOperator.LessThan, n), body);
        return Disp(Eq(F.Id("claim"), All(d, Nat(), All(e, Nat(), All(n, Nat(),
            All(a, Family(n, d), All(phi, Arrow(Matrix(d, d), Matrix(e, e)),
                All(alpha, Real(), All(q, Arrow(Call("Fin", n), Real()), body)))))))));
    }
}
