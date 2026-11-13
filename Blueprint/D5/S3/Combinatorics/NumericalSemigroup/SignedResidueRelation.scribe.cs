using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NumericalSemigroup;

internal sealed class SignedResidueRelationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/NumericalSemigroup/SignedResidueRelation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A signed residue collision constructs a nonzero relation in the reduced toric ideal of the same generators, with total degree at most twice the signed mass bound.",
        H("Signed residues and genuine reduced toric relations"),
        Blocks(
            Paragraph(Text("The target motivating this component is Moscariello–Sammartano, On minimal presentations of numerical monoids, arXiv:2405.19810v1, Conjecture 5.3: for every fixed integer e at least 3, T(e,m) is strictly smaller than D(e,m) for all sufficiently large m. Here e is embedding dimension minus one, and T is the maximum pseudo-Frobenius type over the unrestricted numerical-semigroup class. The registered H route is recorded at https://github.com/the-omega-institute/trureturing/issues/29888#issuecomment-6847353183. This component proves only its finite residue-to-polynomial inference; it does not prove H or the conjecture.")),
            Paragraph(Text("Fix one actual generating list m,g_1,...,g_e. The map sends the multiplicity variable to t^m and every other variable to t raised to its own g_i. The reduced ideal is the image of this very kernel after killing the multiplicity variable. Thus its elements are actual relations for this list; no arbitrary ideal, alternate semigroup realization, symmetry or FGH condition is introduced. The theorem holds for every positive m and every natural generator vector, so applying it to a minimal positive generating list requires no additional hypothesis. Its polynomial presentation is not yet identified in Lean with the completed local Artinian reduction or its associated graded ideal.")),
            Node("signed-residue-positive-mass", "Positive mass", "positiveMass",
                "For every natural e and integer vector v indexed by Fin e, positiveMass(v) is the sum of the natural positive parts max(v_i,0).", DescribeRole.Definition),
            Node("signed-residue-negative-mass", "Negative mass", "negativeMass",
                "For the same vector v, negativeMass(v) is the sum of max(-v_i,0). Both masses belong to the same vector, rather than to independently chosen realizations.", DescribeRole.Definition),
            Node("signed-residue-vectors", "Finite signed vectors", "signedVectors",
                "For every natural e,q, signedVectors(e,q) filters the Cartesian product of the integer intervals [-q,q] by positiveMass(v) at most q and negativeMass(v) at most q. The interval restriction is redundant: each coordinate's positive and negative part is bounded by its corresponding mass. No cardinality formula or eventual lower bound is asserted here.", DescribeRole.Definition),
            Node("signed-residue-bounded-relation", "Disjoint bounded residue relation", "bounded_residue_relation",
                "For every natural e,q,m with m positive, every g:Fin e to the natural numbers, and m strictly smaller than the cardinality of signedVectors(e,q), there exist natural vectors a,b with a different from b, at least one of a_i,b_i zero at every coordinate, both coordinate sums at most 2q, and sum a_i g_i congruent to sum b_i g_i modulo m. Apply finite pigeonhole to v mapped to sum v_i g_i in ZMod m. For a collision v,w, take a_i=max(v_i-w_i,0) and b_i=max(w_i-v_i,0). The inequalities a_i at most max(v_i,0)+max(-w_i,0) and their swapped counterparts bound both sums. The difference a-b=v-w preserves the same generator congruence. This theorem is consumed by exists_bounded_reduced_relation.", DescribeRole.Theorem),
            Node("signed-residue-monomial", "Exponent monomial", "vectorMonomial",
                "For a natural vector a indexed by Fin e, vectorMonomial(a) is the rational multivariate monomial with exponent vector a and coefficient one.", DescribeRole.Definition),
            Node("signed-residue-presentation", "Same-generator presentation map", "semigroupMap",
                "For every natural m and generator vector g indexed by Fin e, semigroupMap(m,g) is the rational algebra evaluation homomorphism from variables Option(Fin e) to a single variable t, sending none to t^m and some(i) to t^(g_i). The target is represented as the rational multivariate polynomial ring with singleton variable type Unit.", DescribeRole.Definition),
            Node("signed-residue-reduction", "Multiplicity-variable reduction", "reduction",
                "For every e, reduction(e) is the rational evaluation homomorphism sending the none variable to zero and each some(i) variable to the surviving variable x_i.", DescribeRole.Definition),
            Node("signed-residue-reduced-ideal", "Reduced genuine toric ideal", "reducedToricIdeal",
                "For the same m,g, reducedToricIdeal(m,g) is the ideal image under reduction(e) of the kernel of semigroupMap(m,g). The kernel and its reduction always use this one generating list.", DescribeRole.Definition),
            Node("signed-residue-toric-relation", "Oriented toric binomial", "toricRelation",
                "For natural exponent vectors a,b and a natural l, toricRelation(a,b,l) is x^a minus x_0^l x^b, with x_0 represented by none and the other variables by some(i). When sum a_i g_i equals sum b_i g_i plus ml, its evaluation under semigroupMap is zero. Reducing it gives x^a-x^b when l is zero and x^a when l is positive.", DescribeRole.Definition),
            Node("signed-residue-reduced-existence", "Nonzero bounded reduced relation", "exists_bounded_reduced_relation",
                "For every natural e,q,m with m positive, every natural vector g:Fin e to the natural numbers, and m strictly smaller than the cardinality of signedVectors(e,q), there exists a rational polynomial f in the variables Fin e such that f belongs to reducedToricIdeal(m,g), f is nonzero, and its total degree is at most 2q. Orient the bounded congruence so sum a_i g_i is at least sum b_i g_i; divisibility supplies a natural l with difference ml. The resulting toric binomial lies in the actual kernel. After reduction, distinct exponent vectors prevent cancellation when l is zero; for positive l the surviving coefficient-one monomial is nonzero. The total-degree bound follows from the two exponent sums. No assumption of a relation or its realizability occurs in the hypotheses.", DescribeRole.Theorem),
            Paragraph(Text("The retained general construction is derived from the registered signed-vector route using the pinned Mathlib finite pigeonhole, ZMod congruence, monomial evaluation, injectivity and degree APIs. It is not a claim of literature novelty. The arithmetic lower bound |V_e(q)| at least the sum over i of binom(e,i)binom(q,i)binom(q,e-i), its eventual strict comparison at q=floor(3r/8), and the connection to the original same-semigroup initial ideal remain to be formalized. The map from a nonzero low-degree reduced relation to a lex pure power, the exact CS23 constrained hyperplane theorem, compressed monomial counts, strict asymptotic thresholds, pseudo-Frobenius type correspondence, original Macaulay D normalization and the final maximum T remain outside this component. In particular neither the cardinality hypothesis nor a cited paper supplies those missing Lean proofs."))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
