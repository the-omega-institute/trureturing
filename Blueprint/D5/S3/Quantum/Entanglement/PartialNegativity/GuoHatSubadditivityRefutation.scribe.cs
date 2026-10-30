using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.PartialNegativity;

internal sealed class GuoHatSubadditivityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Entanglement/PartialNegativity/GuoHatSubadditivityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/guo2024completegenuine");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An equal mixture of two orthogonal maximally entangled states on a 5 × 5 system has reduced function 1/2, whereas both marginals have reduced function 1/5. Thus the subadditivity conjecture (24) for the reduced function of the partial negativity is false.",
        H("Failure of partial-negativity subadditivity"),
        Blocks(
            Node("hhat", "The reduced function of the partial negativity", "hHat", HhatFormula(),
                "Guo, arXiv:2301.00334v3, pp. 4–5: “ĥ(ρ) = √(δ1 δ2), … and δ1, δ2 are the two largest eigenvalues of ρ.” The two entries of Matrix.IsHermitian.eigenvalues₀ are in non-increasing order and counted with multiplicity. The entries at positions 0 and 1 represent δ1 and δ2. If the carrier has fewer than two elements, the value is zero. The condition in the formula supplies the bounds for the two Fin indices.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Guo's subadditivity conjecture (24)", "claim",
                Seq(V("claim"), Sp, Leftrightarrow, Sp, Parenthesized(ClaimBody())),
                "Guo, arXiv:2301.00334v3, p. 5: “We conjecture that ĥ is subadditive, i.e., ĥ(ρAB) ⩽ ĥ(ρA) + ĥ(ρB) (24) holds for any ρAB ∈ S^{AB}. In what follows, we always assume that hF′, hAF, and ĥ are subadditive, and that ĥ is concave.” The carrier Fin dA × Fin dB represents the tensor-product basis. SLDSpectralEnergy.IsDensity means positive semidefinite with trace one. Matrix.traceRight traces out the second factor, and LocalObservationPartialTraceEquivalence.partialTraceFirst traces out the first. Hermitian proof arguments of hHat in the inequality are suppressed: positivity supplies the global proof, Matrix.IsHermitian.traceRight supplies the first marginal proof, and summing the Hermitian entry identities supplies the other.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjectured inequality fails", "result",
                Seq(Neg, Sp, Parenthesized(ClaimBody())),
                "For r = 0, 1, let uᵣ(i,j) be 1 when j = i + r in Fin 5 and 0 otherwise. Put R = (1/10) • (Matrix.vecMulVec u₀ (star u₀) + Matrix.vecMulVec u₁ (star u₁)). Each summand is positive semidefinite. The squared norms of u₀ and u₁ are 5 and their cross dot products vanish. Consequently R has trace one and R² = (1/2) • R. Unitary spectral decomposition makes each eigenvalue either zero or 1/2; trace one and the decreasing eigenvalue order force its first two entries to be 1/2. Both partial traces are (1/5) • 1, so each of their eigenvalues is 1/5. Therefore hHat R = 1/2 while the two marginal values sum to 2/5; the gap is 1/10. All dimensions and all density matrices remain quantified in the negated proposition.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("guo-2024-partial-negativity-hhat-subadditivity"),
                    ResolutionKind.Refuted)))));

    private static Formula HhatFormula()
    {
        Formula n = V("n");
        Formula x = V("X");
        Formula hx = V("hX");
        Formula eigenvalues = new Formula.Subscript(Qualified(hx, "eigenvalues"), D(0));
        Formula first = Apply(eigenvalues, D(0));
        Formula second = Apply(eigenvalues, D(1));
        Formula value = Seq(Word("if"), Sp, D(2), Sp, Leq, Sp,
            Apply(Qualified(V("Fintype"), "card"), n), Sp, Word("then"), Sp,
            Apply(Qualified(V("Real"), "sqrt"), Parenthesized(Seq(first, Sp, Cdot, Sp, second))),
            Sp, Word("else"), Sp, D(0));
        return For(n, V("Type"), Seq(
            OpenBracket, Call("Fintype", n), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", n), CloseBracket, Sp,
            For(x, Call("Matrix", n, n, Cx()),
                For(hx, Qualified(x, "IsHermitian"),
                    Seq(Call("hHat", x, hx), Sp, Eq, Sp, value)))));
    }

    private static Formula ClaimBody()
    {
        Formula a = Call("Fin", V("dA"));
        Formula b = Call("Fin", V("dB"));
        Formula carrier = Parenthesized(Seq(a, Sp, Times, Sp, b));
        Formula density = Apply(Qualified(V("SLDSpectralEnergy"), "IsDensity"), Rho);
        Formula left = Call("hHat", Rho);
        Formula rightA = Call("hHat", Qualified(Rho, "traceRight"));
        Formula rightB = Call("hHat", Apply(
            Qualified(V("LocalObservationPartialTraceEquivalence"), "partialTraceFirst"), Rho));
        Formula inequality = Seq(left, Sp, Leq, Sp, rightA, Sp, Plus, Sp, rightB);
        return For(V("dA"), Nat(), For(V("dB"), Nat(),
            For(Rho, Call("Matrix", carrier, carrier, Cx()),
                Seq(density, Sp, Rightarrow, Sp, inequality))));
    }

    private static DocumentBlock Node(
        string id, string title, string declaration, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Word(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(Formula owner, string name) => Seq(owner, Dot, Word(name));
    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Parenthesized(argument));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula For(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Cx() => Seq(Mathbb, Grp(V("C")));
}
