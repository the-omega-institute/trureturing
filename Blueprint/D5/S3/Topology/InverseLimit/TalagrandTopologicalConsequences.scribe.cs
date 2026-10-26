using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class TalagrandTopologicalConsequencesDocument : IScribeDocumentDefinition
{
    private static Formula V(string s) => F.Id(s);
    private static Formula All(string s, Formula t, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, body);
    private static Formula And(params Formula[] terms)
    {
        var result = terms[^1];
        for (var i = terms.Length - 2; i >= 0; --i)
            result = new Formula.Logic(terms[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Statement()
    {
        var k = Call("ActualFinalLimit", V("hCH"));
        return Disp(All("hCH", V("ContinuumEqualsAlephOne"), And(
            Call("LiteralTalagrandSchemeAtoG", k),
            Call("ClosedCoverSuccessorsAndLiteralLimits", k),
            Call("OriginalFullSignedClopenOscillation", k),
            Call("ContinuousDisjointFiniteImage", k),
            Call("FiniteDisjointHomeomorphicClosedSubspaces", k),
            Call("NoNonemptyCompactBinaryCopyTower", k),
            Call("NoStoneCechEmbeddingInWholeSignedDualUnitBall", k),
            Call("Grothendieck", Call("ContinuousRealFunctions", k)),
            Call("EveryConvergentPointSequenceEventuallyEqualsItsLimit", k),
            Call("NoPointSpaceStoneCechEmbedding", k),
            Call("InfiniteNonFirstCountableNonmetrizable", k))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "CH alone gives one literal Talagrand realization with the full signed and topological endpoints.",
        H("The CH Talagrand construction and its joint endpoints"), Blocks(
            Describe.Lean(DescribeId.Create("actual-ch-talagrand-scheme-and-endpoints"),
                DeclarationHandle.Create("D5/S3/Topology/InverseLimit/TalagrandTopologicalConsequences.actual_CH_Talagrand_scheme_and_endpoints"),
                H("The complete construction on one actual compactum"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/kania2026talagrand")),
                Blocks(
                    Paragraph(Text(
                        "Kania and Kakol, arXiv:2607.06808v2, Problem 8.2 (PDF page 19), ask: Can the prediction principle in Theorem A be weakened from diamond(S) to CH? "
                        + "The theorem has only hCH : continuum = aleph-one as input. Every displayed predicate concerns the single K = (SignedOrdinalRealization.finalPrefix hCH).LimitSpace with its inherited topology. "
                        + "LiteralTalagrandSchemeAtoG denotes the first complete conjunction in the Lean statement: all closed nonempty coordinate carriers, literal onto restrictions, the full initial cubes through omega, the final compact Hausdorff zero-dimensional limit cone and onto projections, the complete whole-birth U/B/nu enumerations, every proper-cutoff original A-F law and every-label measure readback, and the same eta for all support launches and arbitrary signed G lifts with cofinal treatment.")),
                    Paragraph(Text(
                        "All proper stages are compact, Hausdorff, zero-dimensional and metrizable. At each stage at or above omega, closed Y and Z cover the whole stage and the next carrier is literally the range of Boolean insertion from (Y times false) union (Z times true). "
                        + "At each proper limit above omega the carrier is exactly its earlier compatible-thread limit; the final carrier is exactly all threads. The G clopen is exactly the new-coordinate-true cylinder. Its strictly increasing natural columns are fixed before an arbitrary complete norm-one signed lift sequence is chosen. "
                        + "The same eta identifies its every-index source measures and launches; its evaluations exceed one sixth on even columns and equal zero on odd columns. No positivity restriction is added.")),
                    Paragraph(Text(
                        "OriginalFullSignedClopenOscillation quantifies over every regular signed sequence of real total variation one, positive Jordan mass at least one half, and variation concentrated on pairwise disjoint nonempty clopens. One clopen has infinitely many evaluations at least one sixth and infinitely many exact zeros. "
                        + "For every closed A and continuous f : A -> K with A disjoint from range(f), that entire range is finite. Consequently every two disjoint homeomorphic subspaces with one closed are both finite, which implies the precise nonmetrizable closed-copy prohibition in Theorem A. "
                        + "The no-copy-tower clause excludes every sequence of nonempty compact T(n) in K with two disjoint copies of T(n+1) in T(n), without a nesting or infinitude premise.")),
                    Paragraph(Text(
                        "The signed-ball clause quantifies over every continuous h : StoneCech Nat -> WeakDual Real C(K,Real) bounded in the entire strong-dual unit ball and proves h noninjective. It includes principal and free points and both signs. "
                        + "Grothendieck means that for every dual sequence F and functional FInf, pointwise convergence on every continuous real test implies convergence under every continuous real bidual test; no norm bound is an extra hypothesis. "
                        + "Every convergent point sequence is eventually equal to its actual limit. Evaluation embeds K into the signed dual ball, giving the point-space StoneCech obstruction. Surjection onto the omega cube makes K infinite; compactness and the point-sequence conclusion exclude first countability and metrizability.")),
                    Paragraph(Text(
                        "The proof consumes the actual scheme, all geometric equalities, the actual whole signed endpoint theorem, and the continuous finite-image/copy-obstruction theorem. The only construction is the fixed CH run; none of the endpoint hypotheses is assumed. "
                        + "All conclusions refer to this same CH compactum and its original signed scheme. This does not settle Problem 8.1 or the full metrizable quotient problem for Cp(K)."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kania-kakol-2026-problem-8-2-ch-talagrand"),
                    ResolutionKind.Proved)))));
}
