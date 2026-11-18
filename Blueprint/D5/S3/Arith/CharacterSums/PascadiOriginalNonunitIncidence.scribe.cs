using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiOriginalNonunitIncidenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual original parameter/nonzero nonunit endpoint incidences satisfy the smaller outer error bound.",
        H("Normalize the actual nonunit endpoint"),
        Blocks(
            Describe.Lean(DescribeId.Create("pascadi-original-nonunit-endpoint-incidence-count"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalNonunitIncidence.actual_nonunit_endpoint_incidence_count"),
                H("An incidence count with no assumed point-count supplier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix epsilon>0. One positive C works before all primes p and positive X<=Y,H with H^2=XY, p^2<=XY and 2Y<p^2. Let I be a finite set of actual integer incidences ((w,t),(a,d)), both vectors in the literal X,Y rectangle. Require w,t units modulo p^3, p^3 dividing w*d-t*a, a nonzero endpoint (a,d), and a nonunit first endpoint coordinate modulo p^3. Then card(I)<=C*p^epsilon*(XY/p+(XY)^2/p^4). No word condition, longness assumption or unit-shortest-vector assumption is needed for this incidence estimate.")),
                    Paragraph(Text("Nonunit a implies p divides a, and the actual congruence with unit w implies p divides d. The integer vector z0=(a/p,d/p) is nonzero, lies in the actual index-p-squared lattice and in the X/p,Y/p rectangle, and recovers the actual endpoint injectively by multiplication by p. Choose an actual reduced prime-square basis only at each parameter appearing in I. Its shortest squared length is at most Q(z0)<=2XY/p^2. The existing actual lattice-section count bounds the normalized endpoint fiber by a fixed multiple of 1+2H/(p*sigma), because XY/p^4<1. Rescale the metric inputs to 2X,2Y,2H, which preserves Q, and consume the short-only weight average. Sum the genuine finite fibers over the actual original parameters. The proof does not multiply by a separate number of slope lifts."))),
                DescribeRole.Theorem),
            Paragraph(Text("The next module uses the original unit-right-side word to recover the opposite endpoint and applies this incidence bound to actual ReturnRows. This intermediate result alone does not restore all six-variable solutions or close the Pascadi conjecture.")))));
}
