using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class MersennePhaseNoncyclicFamilyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Circle/MersennePhaseNoncyclicFamily.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every d at least three with 19 not dividing 2^(d+1)-3, all physical integer-zero subsets are uniquely complete phase unions with the two exceptional phases selected together; their exact number is 2^(d-1).",
        H("The admissible three-phase Mersenne family"),
        Blocks(
            Paragraph(Text("Fix any natural d at least three, put g=2^d-1, m=2^(d+1)-3 and N=2^(3d)-1, and assume 19 does not divide m. The physical source is SourceWidth.actualSource(3d,g*m). Every subset of Fin(3d) is in the domain. For B in Finset(Fin(d)), phaseLift(d,B) consists of every original label i with i.val modulo d in B: a selected phase retains the three distinct labels j, j+d and j+2d, even when source values repeat. The pair condition means that d-3 belongs to B exactly when d-1 belongs to B.")),
            Describe.Lean(DescribeId.Create("actual-zero-iff-phase-pair"),
                DeclarationHandle.Create(Prefix + "actual_zero_iff_phase_pair"),
                H("Unique physical zero-subset classification"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The gcd identity gcd(g*m,N)=g*gcd(m,19) follows from N=g*(2^(2d)+2^d+1), oddness of m and 4*(2^(2d)+2^d+1)=m^2+8*m+19. The domain condition makes this gcd equal to g. A literal integer-zero sum therefore forces N/g to divide the existing binary mask. The already proved minus-seed reduced-divisibility bridge and actual_zero_iff_rotation force invariance under rotation by d. No modular-zero condition is used as an assumed equivalence to the physical sum.")),
                    Paragraph(Text("Rotation by d carries j to j+d to j+2d. Euclidean division exhausts these three representatives, so the physical set is exactly phaseLift of its first-representative selection. Reading back that first representative is a left inverse, which proves the unique witness. Finset.sum_fiberwise_eq_sum_filter then transports the actual physical sum to the phase sum. MersennePhaseThreeTrace.actual_phase_trace gives literal integer traces +N at d-3, -N at d-1 and zero elsewhere. Since N is nonzero, cancellation is exactly the pair condition, proving both directions."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-zero-subsets-card"),
                DeclarationHandle.Create(Prefix + "actual_zero_subsets_card"),
                H("Exactly 2^(d-1) physical subsets"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The physical phaseLift and first-representative maps are mutual inverses on their exact zero filters. Finset.card_nbij' transports the cardinality without identifying equal-valued labels. Apply TernaryPhaseZeroCount.zero_subsets_card to the literal phase weights: one +1, one -1 and d-2 zero labels give 2^(d-2)*choose(2,1)=2^(d-1). No generic counting or Boolean framework is added.")),
                    Paragraph(Text("Empty and full subsets, nonunit seeds, repeated values, d=3, d=4 and arbitrary large admissible d remain included. The condition excluding the factor 19 is used in the phase-union inference and is not removed by the trace theorem, which itself holds for every d at least three. At excluded parameters this argument makes no claim that every zero subset is a phase union. These are physical subset classification and count theorems, not a full Circle result, a Boolean-algebra/stabilizer theorem or a literature-novelty claim. Existing minus/TwoBit count audits at Nat.gcd remain unfinished under issue https://github.com/the-omega-institute/trureturing/issues/11434; their mathematical proofs and audit sources are preserved."))),
                DescribeRole.Theorem)), []));
}
