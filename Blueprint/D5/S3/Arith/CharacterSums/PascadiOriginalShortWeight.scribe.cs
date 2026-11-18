using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiOriginalShortWeightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Only actual short prime-square lattices contribute to the smaller original-parameter incidence bound.",
        H("The short part of the physical weight average"),
        Blocks(
            Describe.Lean(DescribeId.Create("pascadi-original-short-weight-subpower"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalShortWeight.actual_short_physical_weight_subpower"),
                H("Remove the large-length area term"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every epsilon>0, a single positive C works for all primes p, positive X<=Y and H with H^2=XY and H>=p. Assume Y<p^3 and XY<2p^4. Let s be any finite set of actual original integer parameters (w,t) in the literal X,Y rectangle, with both parameters units modulo p^2. For each member, U is the first vector of an actual reduced basis of the index-p-squared congruence lattice, and Q(U)<=XY/p^2. Then the sum of 1+H/(p*sqrt(Q(U))) over s is at most C*p^epsilon*(XY/p+(XY)^2/p^4). The basis witness is required only at parameters actually in s.")),
                    Paragraph(Text("The existing short-vector unit theorem gives a genuine lower length bound. Cover all actual shortest lengths by dyadic annuli between 1 and H/p, then consume the existing actual_shortest_vector_scale_weight on each annulus. The length-dependent terms sum geometrically, giving XY/p^2 and (XY)^2/p^4; the scale-independent term costs XY/p times the number of annuli. The number is bounded by a fixed multiple of log(2p), and log(p)<=p^epsilon/epsilon absorbs it into one uniform constant. There is no large-shortest-length stratum in s, so the unweighted XY term in the unrestricted average is not incurred."))),
                DescribeRole.Theorem),
            Paragraph(Text("This is the short-parameter estimate used to count actual removed nonunit endpoints. It does not count freely selected slope lifts and does not establish the full original six-variable conjecture.")))));
}
