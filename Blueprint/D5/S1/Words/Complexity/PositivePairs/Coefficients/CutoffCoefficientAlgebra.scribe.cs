using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.PositivePairs.Coefficients;

internal sealed class PositivePairsCoefficientsCutoffCoefficientAlgebraDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite cutoff word coefficients form a truncated multiplicative algebra.",
        H("CutoffCoefficientAlgebra"),
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
                "Under the same positive-degree hypothesis, the same finite geometric series is also a left inverse."))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
