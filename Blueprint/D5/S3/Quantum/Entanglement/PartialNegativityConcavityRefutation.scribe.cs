using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class PartialNegativityConcavityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Entanglement/PartialNegativityConcavityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/guo2023partialnorm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The function ĥ(ρ) = √(δ₁δ₂) of the two largest eigenvalues δ₁ ≥ δ₂ of a density matrix, the reduced function of the partial negativity, is not concave: the commuting qutrit states diag(1/2, 1/3, 1/6) and diag(1/2, 1/6, 1/3) have ĥ = √(1/6), and their midpoint diag(1/2, 1/4, 1/4) has ĥ = √(1/8).",
        H("Non-concavity of the reduced function of the partial negativity"),
        Blocks(
            Node("hhat", "The reduced function of the partial negativity", "hhat", Disp(HhatFormula()),
                "For a complex d × d matrix A, let δ₁ ≥ δ₂ ≥ ⋯ be the real parts of the roots of its characteristic polynomial, taken with multiplicity and sorted in decreasing order; ĥ(A) = √(δ₁δ₂). Here roots(p) is the multiset of complex roots of p, map(re, s) the multiset of real parts, sort(s, ge) the list obtained by sorting the multiset s with respect to ≥, and getD(l, n, x) the entry of the list l at position n, counted from 0, or x when the list is too short. For a Hermitian matrix the roots are real and the sorted list is its list of eigenvalues in decreasing order, counted with multiplicity, so δ₁ and δ₂ are its two largest eigenvalues. For a pure bipartite state with decreasing Schmidt coefficients λ₁ ≥ λ₂ ≥ ⋯ the partial negativity is λ₁λ₂, which equals ĥ of either reduced state because the eigenvalues of the reduced state are the λⱼ².",
                DescribeRole.Definition, Lit()),
            Node("claim", "The conjectured concavity", "claim", Disp(ClaimFormula()),
                "The conjecture of arXiv:2212.06521v6 that ĥ is concave: for every dimension d ≥ 2, all positive semidefinite ρ and σ of trace one and every real t in [0, 1], t ĥ(ρ) + (1 − t) ĥ(σ) ≤ ĥ(tρ + (1 − t)σ). The products tρ and (1 − t)σ are multiplications of a complex matrix by a real number.",
                DescribeRole.Definition, Lit()),
            Node("result", "The reduced function of the partial negativity is not concave", "result",
                Disp(new Formula.Not(V("claim"))),
                "Take d = 3, t = 1/2, ρ = diag(1/2, 1/3, 1/6) and σ = diag(1/2, 1/6, 1/3). Both are positive semidefinite with trace one. The characteristic polynomial of a diagonal matrix is the product of the factors X − dᵢ, so its characteristic roots, sorted decreasingly, are the sorted diagonal entries: (1/2, 1/3, 1/6) for ρ and for σ, and (1/2, 1/4, 1/4) for the midpoint diag(1/2, 1/4, 1/4). Hence ĥ(ρ) = ĥ(σ) = √(1/6), while ĥ of the midpoint is √(1/8) < √(1/6). The second-largest eigenvalue 1/3 belongs to different eigenvectors of ρ and σ, and mixing lowers it to 1/4 while the largest eigenvalue stays 1/2.",
                DescribeRole.Theorem, Repo()))));

    private static Formula HhatFormula()
    {
        Formula sorted = Call("sort", Call("map", V("re"), Call("roots", Call("charpoly", V("A")))), V("ge"));
        Formula first = Call("getD", sorted, D(0), D(0));
        Formula second = Call("getD", sorted, D(1), D(0));
        Formula value = Seq(Sqrt, Grp(Seq(first, Sp, second)));
        return For(V("d"), Nat(), For(V("A"), MatType(), Equal(Call("hhat", V("A")), value)));
    }

    private static Formula ClaimFormula()
    {
        Formula mix = Seq(V("t"), Sp, Rho, Sp, Plus, Sp, Parenthesized(Seq(D(1), Sp, Minus, Sp, V("t"))), Sp,
            SigmaLower);
        Formula inequality = Seq(
            V("t"), Sp, Call("hhat", Rho), Sp, Plus, Sp,
            Parenthesized(Seq(D(1), Sp, Minus, Sp, V("t"))), Sp, Call("hhat", SigmaLower), Sp, Leq, Sp,
            Call("hhat", mix));
        Formula inT = For(V("t"), Real(), Imp(Seq(D(0), Sp, Leq, Sp, V("t")),
            Imp(Seq(V("t"), Sp, Leq, Sp, D(1)), inequality)));
        Formula states = Imp(Call("PosSemidef", Rho), Imp(Equal(Call("tr", Rho), D(1)),
            Imp(Call("PosSemidef", SigmaLower), Imp(Equal(Call("tr", SigmaLower), D(1)), inT))));
        Formula body = For(V("d"), Nat(), Imp(Seq(D(2), Sp, Leq, Sp, V("d")),
            For(Seq(Rho, Comma, Sp, SigmaLower), MatType(), states)));
        return IffOf(V("claim"), Parenthesized(body));
    }

    private static AssessedProvenance Lit() => AssessedProvenance.FromLiterature(Source);
    private static AssessedProvenance Repo() => AssessedProvenance.FromRepo(Source);

    private static DocumentBlock Node(
        string id, string title, string declaration, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Cx() => Seq(Mathbb, Grp(V("C")));
    private static Formula MatType() => Call("Matrix", Call("Fin", V("d")), Call("Fin", V("d")), Cx());
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula For(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, name, Colon, Sp, type, Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula body) => Seq(premise, Sp, Rightarrow, Sp, body);
    private static Formula IffOf(Formula left, Formula right) => Seq(left, Sp, Leftrightarrow, Sp, right);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
}
