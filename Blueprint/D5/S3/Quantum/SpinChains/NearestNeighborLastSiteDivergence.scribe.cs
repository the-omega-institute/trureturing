using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class NearestNeighborLastSiteDivergenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/NearestNeighborLastSiteDivergence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/enciso2007nearestneighbor");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The last site of the cyclic nearest-neighbor QES chain exceeds every fixed real bound for all sufficiently large chain lengths.",
        H("Divergence of the last site of the nearest-neighbor QES chain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nearest-neighbor-last-site-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The last-site question"),
                StatementSource.FromAuthor(Disp(Seq(Operatorname, Grp(F.Id("claim")), Sp, Iff, Sp,
                    Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The paper asks in §2, printed p. 9, before Eq. (19): \"It is also of interest to determine whether the position of the last spin tends to infinity as N → ∞, since according to our interpretation of the chain’s geometry the number 2ξN/π is the radius of the circle on which the spins lie.\" The displayed proposition expresses divergence uniformly over all strictly increasing solutions of the cyclic equations (6). The symbol xi denotes ξ : Fin N → ℝ; zero-based index N − 1 is the source's site ξN. Subtraction N − 1 is truncated natural subtraction. The notation ⟨N − 1⟩ denotes the Fin N index with its proof component suppressed; 3 ≤ N supplies that proof. Sites is the cyclic site predicate of NearestNeighborFreezingUniqueMinimum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nearest-neighbor-last-site-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The last site diverges"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reflection and negation preserve the cyclic equations and the increasing chamber. A maximum-coordinate comparison gives uniqueness, hence the first and last coordinates are −R and R with R > 0. Summing the first k equations retains the wrap-around reciprocal and gives 1/k < R(ξk − ξ(k−1)) in zero-based indices, for 1 ≤ k < N. Summing these gap estimates yields H_(N−1) < 2R², where H_m = Σ_(j=1)^m 1/j. Harmonic divergence then gives the displayed conclusion. Increasing solutions exist for every N ≥ 3 by NearestNeighborFreezingUniqueMinimum.result. The sharper inverse-error-function approximation in Eq. (19) is a separate question."))),
                DescribeRole.Theorem)),
        []));

    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Ex(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Fn(Formula n) => new Formula.TypeArrow(Call("Fin", n), Real());
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula ClaimBody()
    {
        var b = F.Id("B");
        var n0 = F.Id("N0");
        var n = F.Id("N");
        var xi = F.Id("xi");
        var index = Seq(Langle, Sp,
            new Formula.Binary(n, FormulaBinaryOperator.Subtract, D(1)), Sp, Rangle);
        var last = new Formula.Apply(xi, [index]);
        var hypotheses = Seq(D(3), Sp, Leq, Sp, n, Sp, Rightarrow, Sp,
            Call("StrictMono", xi), Sp, Rightarrow, Sp,
            Call("Sites", xi), Sp, Rightarrow, Sp,
            b, Sp, Lt, Sp, last);
        return All("B", Real(), Ex("N0", Nats(), All("N", Nats(),
            Parenthesized(Seq(n0, Sp, Leq, Sp, n, Sp, Rightarrow, Sp,
                All("xi", Fn(n), Parenthesized(hypotheses)))))));
    }
}
