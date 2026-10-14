using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Walks;
internal sealed class RieszWalkSelfSimilarityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef HK = LibraryNoteRef.Create("D5/L/QuantumBounds/hanaoka2021rieszwalk");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Riesz moments, orthogonal Laurent polynomials and scale-four projection identities.",
        H("RieszWalkSelfSimilarity"), Blocks(
            Node("D5/S3/Quantum/Walks/RieszWalkSelfSimilarity.prob", "prob", Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, F.Id("Set"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma, Sp, Seq(Operatorname, Grp(F.Id("prob"))), Sp, F.Id("t"), Sp, F.Id("S"), Sp, Eq, Sp, Sum, Sp, Apos, Sp, Parenthesized(Seq(F.Id("y"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Seq(Operatorname, Grp(F.Id("if"))), Sp, Call("Nat.cast", F.Id("y")), Sp, Slash, Sp, new Formula.Relation(Call("Nat.cast", F.Id("t")), FormulaRelationOperator.MemberOf, Seq(F.Id("S"), Sp, Seq(Operatorname, Grp(F.Id("then"))), Sp, Seq(Operatorname, Grp(F.Id("mu"))), Sp, F.Id("t"), Sp, F.Id("y"), Sp, Seq(Operatorname, Grp(F.Id("else"))), Sp, new Formula.Number(0))))),
                "The sum is over all natural-number sites. Finite propagation makes only finitely many terms nonzero. Rational division gives the normalized site position.", DescribeRole.Definition, AssessedProvenance.FromLiterature(HK)),
            Node("D5/S3/Quantum/Walks/RieszWalkSelfSimilarity.Tset", "Tset", Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Seq(Operatorname, Grp(F.Id("Tset"))), Sp, F.Id("n"), Sp, F.Id("k"), Sp, Eq, Sp, Seq(Operatorname, Grp(F.Id("if"))), Sp, F.Id("k"), Sp, Eq, Sp, new Formula.Number(0), Sp, Seq(Operatorname, Grp(F.Id("then"))), Sp, Seq(OpenBrace, new Formula.Number(0), CloseBrace), Sp, Seq(Operatorname, Grp(F.Id("else"))), Sp, Qualified("Set", "Ioc"), Sp, Parenthesized(Seq(Parenthesized(Seq(Call("Nat.cast", F.Id("k")), Sp, Minus, Sp, new Formula.Number(1))), Sp, Slash, Sp, Call("Nat.cast", F.Id("n")))), Sp, Parenthesized(Seq(Call("Nat.cast", F.Id("k")), Sp, Slash, Sp, Call("Nat.cast", F.Id("n")))))),
                "Section 4, Conjecture 4.2, arXiv PDF p. 12: “Let ℤ_> = {1, 2, 3, …}. For each n ∈ ℤ_>, we put T₀(n) = {0}, and Tₖ(n) = ((k − 1)/n, k/n] (1 ≤ k ≤ n). Then, for the measure of the Riesz walk with initial state of Ψ₀ = [1, 0]ᵀδ₀, P(X₂ₜ/(2t) ∈ Tₖ(t)) = P(X₈ₜ/(8t) ∈ Tₖ(t)), for any t ∈ ℤ_>.” The case k=0 is a singleton; every other case is left-open and right-closed.", DescribeRole.Definition, AssessedProvenance.FromLiterature(HK)),
            Node("D5/S3/Quantum/Walks/RieszWalkSelfSimilarity.claim", "claim", Disp(Seq(Seq(Operatorname, Grp(F.Id("claim"))), Sp, Iff, Sp, Forall, Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, new Formula.Number(1), Sp, Leq, Sp, F.Id("t"), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("k"), Sp, Leq, Sp, F.Id("t"), Sp, To, Sp, Seq(Operatorname, Grp(F.Id("prob"))), Sp, Parenthesized(Seq(new Formula.Number(2), Sp, Cdot, Sp, F.Id("t"))), Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("Tset"))), Sp, F.Id("t"), Sp, F.Id("k"))), Sp, Eq, Sp, Seq(Operatorname, Grp(F.Id("prob"))), Sp, Parenthesized(Seq(new Formula.Number(8), Sp, Cdot, Sp, F.Id("t"))), Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("Tset"))), Sp, F.Id("t"), Sp, F.Id("k"))))),
                "Section 4, Conjecture 4.2, arXiv PDF p. 12: “Let ℤ_> = {1, 2, 3, …}. For each n ∈ ℤ_>, we put T₀(n) = {0}, and Tₖ(n) = ((k − 1)/n, k/n] (1 ≤ k ≤ n). Then, for the measure of the Riesz walk with initial state of Ψ₀ = [1, 0]ᵀδ₀, P(X₂ₜ/(2t) ∈ Tₖ(t)) = P(X₈ₜ/(8t) ∈ Tₖ(t)), for any t ∈ ℤ_>.” Here t and k are natural numbers, 1 ≤ t and k ≤ t. The two coordinates at site x are 2x and 2x+1. The intervals have rational endpoints and probabilities are real.", DescribeRole.Definition, AssessedProvenance.FromLiterature(HK)),
            Node("D5/S3/Quantum/Walks/RieszWalkSelfSimilarity.result", "result", Disp(Seq(Operatorname, Grp(F.Id("claim")))),
                "Cumulative probabilities are squared norms of projections onto the Laurent windows. Fourth-power decimation and the parity-weighted projection identity make these norms equal at the two scales. Interval differences give the assertion, including the singleton interval at the origin.", DescribeRole.Theorem, AssessedProvenance.FromRepo(HK),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hanaoka-konno-2021-riesz-walk-self-similarity"),
                    ResolutionKind.Proved))), []));
    private static DocumentBlock Node(string handle, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("hk-" + handle.Replace('/', '-').Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(handle), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Qualified(name.Split('.')), [.. args]);
    private static Formula Qualified(params string[] parts) => Seq(Operatorname, Grp(Seq([.. parts.Select((x,i) =>
        i == 0 ? F.Id(x) : Seq(Dot, F.Id(x)))])));
}
