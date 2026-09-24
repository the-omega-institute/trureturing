using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class PositivePairWordCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/PositivePairWordCoefficients";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Magnus polynomials turn the full recursive positive-pair family into filtered coefficient differences whose first live term is a Lyndon-bracket direction.",
        H("Actual Positive-Pair Magnus Coefficients"),
        Blocks(
            Paragraph(Text(
                "Magnus expansions and shuffle or infiltration identities are classical context, "
                + "but the complete recursively indexed positive-pair construction below is a "
                + "repository route. Indices are retained even when two evaluated pairs coincide.")),
            D("rational-word-polynomial", "RationalWordPolynomial", "Rational word algebra",
                "RationalWordPolynomial A abbreviates MonoidAlgebra Q (FreeMonoid A).", DescribeRole.Definition),
            D("to-rational-word-polynomial", "toRationalWordPolynomial", "Extend integer coefficients to rationals",
                "This ring homomorphism maps the integral WordPolynomial coefficients through Int.castRingHom Q while retaining every word monomial.", DescribeRole.Definition),
            D("cutoff-word", "CutoffWord", "Words through a cutoff degree",
                "CutoffWord A r is the subtype of free words whose length is at most r.", DescribeRole.Definition),
            D("cutoff-coefficients", "CutoffCoefficients", "Finite cutoff coefficient vectors",
                "CutoffCoefficients A r is the function space CutoffWord A r -> Q.", DescribeRole.Definition),
            D("cutoff-restriction", "cutoffRestriction", "Restrict a polynomial to bounded words",
                "cutoffRestriction r p evaluates the coefficient of p at each free word of length at most r.", DescribeRole.Definition),
            D("cutoff-lift", "cutoffLift", "Lift bounded coefficients by zero",
                "For finite A, cutoffLift r extends a CutoffCoefficients vector to the full rational word algebra and assigns zero outside the cutoff subtype.", DescribeRole.Definition),
            D("cutoff-mul", "cutoffMul", "Split convolution in the cutoff algebra",
                "cutoffMul r p q at a target word sums p(prefix)*q(suffix) over every cut from zero through the target length.", DescribeRole.Definition),
            D("cutoff-one", "cutoffOne", "The empty-word unit vector",
                "cutoffOne r is the restriction of the multiplicative unit of the rational word algebra.", DescribeRole.Definition),
            D("cutoff-restriction-mul", "cutoffRestriction_mul", "Restriction preserves multiplication",
                "For every cutoff r and rational word polynomials p,q, restriction of p*q equals cutoffMul r of their restrictions.", literature: true),
            D("vanishes-below", "VanishesBelow", "Filtration vanishing",
                "VanishesBelow r d p means p is zero on every cutoff word of length strictly below d.", DescribeRole.Definition),
            D("cutoff-mul-vanishes-below", "cutoffMul_vanishesBelow", "Filtration degrees add",
                "If p vanishes below d and q below e, their cutoff product vanishes below d+e."),
            D("cutoff-pow", "cutoffPow", "Powers inside the cutoff algebra",
                "cutoffPow r p 0=cutoffOne r and cutoffPow r p (n+1)=cutoffMul r p (cutoffPow r p n).", DescribeRole.Definition),
            D("cutoff-pow-restriction", "cutoffPow_eq_restriction_pow", "Cutoff powers are genuine restrictions",
                "For finite A and every n, cutoffPow r p n equals cutoffRestriction r of (cutoffLift r p)^n."),
            D("cutoff-pow-vanishes-below", "cutoffPow_vanishesBelow", "Positive degree accumulates",
                "If p vanishes below degree one, then its nth cutoff power vanishes below degree n."),
            D("cutoff-geometric-inverse", "cutoffGeometricInverse", "Finite geometric inverse",
                "For finite A, cutoffGeometricInverse r c restricts the finite sum of powers of cutoffLift r (-c) from zero through r.", DescribeRole.Definition),
            D("cutoff-mul-geometric-inverse", "cutoffMul_geometricInverse", "Right inverse of one plus a tail",
                "If c vanishes below degree one, cutoffMul r (cutoffOne r+c) (cutoffGeometricInverse r c)=cutoffOne r."),
            D("geometric-inverse-cutoff-mul", "geometricInverse_cutoffMul", "Left inverse of one plus a tail",
                "Under the same positive-degree hypothesis, the same finite geometric series is also a left inverse."),
            D("magnus-polynomial", "magnusPolynomial", "Actual positive-word Magnus polynomial",
                "magnusPolynomial []=1 and magnusPolynomial (a::w)=(1+X_a)*magnusPolynomial w, preserving source order.", DescribeRole.Definition, true),
            D("magnus-polynomial-append", "magnusPolynomial_append", "Magnus is multiplicative on concatenation",
                "For all finite words left,right, the Magnus polynomial of left++right is the product of their Magnus polynomials.", literature: true),
            D("magnus-coeff-scattered-count", "magnusPolynomial_coeff_scatteredCount", "Magnus coefficients are scattered counts",
                "With decidable equality on A, the coefficient at pattern in magnusPolynomial source is exactly the natural scatteredCount pattern source, cast to Z.", literature: true),
            D("word-abelianization", "wordAbelianization", "Degree-one letter sum",
                "wordAbelianization recursively sums the singleton wordMonomial for each source letter and maps the empty word to zero.", DescribeRole.Definition),
            D("word-abelianization-append", "wordAbelianization_append", "Abelianization is additive",
                "wordAbelianization (left++right) is the sum of the two word abelianizations."),
            D("word-abelianization-singleton", "wordAbelianization_coeff_singleton", "Singleton coefficients count letters",
                "With decidable equality, the coefficient of [b] in wordAbelianization source is scatteredCount [b] source, cast to Z."),
            D("word-abelianization-empty", "wordAbelianization_coeff_empty", "No empty coefficient",
                "For every source, wordAbelianization source has coefficient zero at the empty free word."),
            D("positive-pair-index", "PositivePairIndex", "Full recursive choice index",
                "PositivePairIndex A r abbreviates Fin r -> A. Distinct indices remain distinct even if their evaluated word pairs coincide.", DescribeRole.Definition),
            D("positive-pair-words", "positivePairWords", "Actual recursive positive pairs",
                "Level zero is ([],[]), level one is ([a],[]), and a successor step sends (u,v) and a to (u++[a]++v, v++[a]++u).", DescribeRole.Definition),
            D("cutoff-magnus", "cutoffMagnus", "Actual Magnus cutoff",
                "For finite A, cutoffMagnus r source is the rational coefficient extension of the actual Magnus polynomial restricted through degree r.", DescribeRole.Definition),
            D("positive-pair-ratio", "positivePairRatio", "Actual positive-pair Magnus ratio",
                "For independent cutoff and level parameters, positivePairRatio is cutoffMagnus(u) multiplied by the finite geometric inverse of cutoffMagnus(v)-1 for the actual pair (u,v).", DescribeRole.Definition),
            D("positive-pair-ratio-filtration", "full_positivePair_ratio_filtration", "Full indexed family agrees below its level",
                "For every finite alphabet, cutoff, level r, and full PositivePairIndex, both the actual cutoff-Magnus difference M(u)-M(v) and the ratio minus one vanish below r. Duplicate pairs and zero leading directions remain in the quantified family."),
            D("successor-leading-bracket", "full_positivePair_successor_leading_bracket", "Successor difference is a commutator",
                "For finite A with decidable equality and index at level r+2, let c be the preceding actual cutoff-Magnus difference and x the rationalized abelianization of the previous right word plus X_a. The successor Magnus difference equals cutoffMul c x - cutoffMul x c in cutoff r+2."),
            D("successor-ratio-leading-bracket", "full_positivePair_successor_ratio_leading_bracket", "The ratio has the same leading commutator",
                "Under the same hypotheses and definitions, positivePairRatio at level and cutoff r+2 minus cutoffOne equals cutoffMul c x - cutoffMul x c."),
            D("positive-pair-coefficient-checkpoint", "full_positivePair_coefficient_checkpoint", "Actual coefficient checkpoint",
                "For every finite alphabet with decidable equality, level r, and full index: when 2<=r both actual pair words are nonempty and equally long; for every cutoff word, the rational Magnus-difference coefficient is exactly the difference of the two frozen scattered counts.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Words/Complexity/LyndonStandardBracket")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Words/Complexity/VivionBinomialConverseFails")),
        ]));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
