using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class KhetanLineFactorCancellationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/KhetanLineFactorCancellation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Laurent line divisibility supplies the geometric fiber equations.",
        H("From Laurent line factors to cancellation on actual lattice fibers"),
        Blocks(
            Paragraph(Text(
                "The coefficient domain is a field R with a unital ring homomorphism "
                + "ρ:R→ℂ. This includes real line factors via the real-to-complex embedding "
                + "and complex line factors via the identity. The Laurent ring is the existing "
                + "AddMonoidAlgebra, with the existing lineLaurent embedding k↦ku and the "
                + "existing exactCoverMask(F)=Σ[f∈F]X^(−f). Nonunit is taken over R: a "
                + "nonzero scalar monomial is excluded. The direction u is primitive in the "
                + "integer lattice, with the exact determinant and Bézout coordinate used "
                + "by KhetanLatticeGeometry.")),
            Describe.Lean(
                DescribeId.Create("line-factor-fiber-cancellation"),
                DeclarationHandle.Create(Owner + "line_factor_fiber_cancellation"),
                H("A genuine line divisor supplies one root for every occupied fiber"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any finite tile F and primitive u, let A be a nonzero nonunit "
                        + "one-variable Laurent polynomial over R. Assume the actual divisor "
                        + "lineLaurent(u,A) divides the coefficient-cast exactCoverMask(F). "
                        + "The result constructs ζ∈ℂˣ with eval₂(ρ,ζ,A)=0 and proves "
                        + "FiberCancellation(F,u,ζ⁻¹). No root or cancellation equation "
                        + "is a hypothesis, and neither unit modulus nor a root-of-unity "
                        + "restriction is imposed. This theorem does not require six points "
                        + "or full integer-difference span.")),
                    Paragraph(Text(
                        "Mathlib's Laurent localization gives q.toLaurent=A·T^n. Removing "
                        + "the full zero-root multiplicity gives q=X^m s with s(0)≠0. "
                        + "If s were constant, q.toLaurent and then A would be units, a "
                        + "contradiction. The field homomorphism ρ is injective, so s.map(ρ) "
                        + "is nonconstant and retains its nonzero constant term. The "
                        + "fundamental theorem of algebra supplies a nonzero complex root ζ. "
                        + "Evaluation of the cleared identity and invertibility of T^n "
                        + "give eval₂(ρ,ζ,A)=0.")),
                    Paragraph(Text(
                        "The weighted projection is a ring homomorphism sending aX^z to "
                        + "ρ(a)ζ^fiberCoordinate(u,z)Y^det(u,z). Additivity of the two integer "
                        + "coordinates makes it multiplicative. Primitivity gives "
                        + "fiberCoordinate(u,ku)=k and det(u,ku)=0, so the line factor "
                        + "projects to the constant eval₂(ρ,ζ,A)=0. Actual divisibility "
                        + "therefore makes the projected tile mask zero.")),
                    Paragraph(Text(
                        "Its coefficient at −det(u,p) is exactly the sum of "
                        + "ζ^(−fiberCoordinate(u,q)) over q in the actual fiber F∩(p+ℤu). "
                        + "Multiplication by ζ^fiberCoordinate(u,p) converts this to the "
                        + "sum of (ζ⁻¹)^fiberCoordinate(u,q−p). This proves the relative "
                        + "positive-offset cancellation required by the geometry and "
                        + "explicitly accounts for the negative-mask sign convention."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-line-factors-orbit-closure-periodic"),
                DeclarationHandle.Create(Owner + "two_line_factors_orbit_closure_periodic"),
                H("The two-direction factor branch reaches the given orbit closure"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume F has six points, its integer differences span ℤ², and "
                        + "T is the given exact-cover complement. Suppose two nonzero "
                        + "nonunit Laurent polynomials over the same coefficient field "
                        + "embed as actual divisors of the tile mask in primitive directions "
                        + "u and v with det(u,v)≠0. The first theorem supplies both "
                        + "cancellation roots. They are passed directly to "
                        + "KhetanLatticeGeometry.two_direction_orbit_closure_periodic.")),
                    Paragraph(Text(
                        "The conclusion gives one nonzero lattice vector t that is a "
                        + "period of every configuration in the shift orbit closure of "
                        + "the original indicator of T. This is the two-direction branch "
                        + "of the given-orbit-closure question in arXiv:2607.09830v2, §3.5. "
                        + "The existence or absence of line factors in other branches is "
                        + "a separate obligation; this result does not assert the full "
                        + "six-cell conjecture."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The reused Laurent localization and evaluation APIs are in Mathlib's "
                + "Algebra/Polynomial/Laurent.lean; zero-root removal is "
                + "Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd, and complex "
                + "root existence is Complex.exists_root. These are reused at the pinned "
                + "Mathlib revision 56a005855ea17e0b0958f73ec801ae140b0a1679. The "
                + "existing action suppliers retain their software attribution in "
                + "KhetanAnnihilator and Library/FiniteGeometry/ho2026nivat.md. The construction "
                + "here is a Laurent specialization bridge to the actual geometric "
                + "consumer; no literature novelty is claimed for root extraction."))),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/KhetanLatticeGeometry"))]));
}
