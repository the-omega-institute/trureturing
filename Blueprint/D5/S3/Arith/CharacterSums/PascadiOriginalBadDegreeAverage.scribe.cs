using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiOriginalBadDegreeAverageDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual long reduced charts supply their heights, and their derivative defects have the original physical parameter average.",
        H("The actual long-chart bad-degree average"),
        Blocks(
            Describe.Lean(DescribeId.Create("pascadi-original-long-chart-area-height-one-le"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalBadDegreeAverage.long_chart_area_height_one_le"),
                H("A genuine long chart supplies a positive normalized area height"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a prime p, positive X,Y,H with H squared=XY, and a genuine reduced index-p-cubed basis B satisfying p^6<H^2*Q(B.R), the normalized area height 32XY/p^3 is at least one. The actual long-scale bounds give 2<J2<=J1 and J1*J2=32XY/p^3. This consumed helper transfers the old numerical-cutoff interfaces to seventh height for actual nonempty long-chart families; no corresponding claim is made for arbitrary small area data without such a chart."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("pascadi-original-long-bad-degree-subpower-seventh"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalBadDegreeAverage.actual_long_bad_degree_subpower_seventh"),
                H("Actual long charts with only the seventh-height cutoff"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every epsilon>0 a uniform positive C bounds the actual long-chart maximum derivative-zero degree by C*p^epsilon*(1+6H/(p*sqrt(Q(R2)))). Retain the actual original prime-cube reduced long basis, prime-square reduced basis, literal physical boxes, anchor identity, original word and all original units. The only scale separation replacing the previous three numerical cutoffs is seventhHeightConstant*(32XY/p^3)^7<p^5. The genuine reduced basis supplies J1=8H/sigma, J2=4H*sigma/p^3 and J1*J2=32XY/p^3; the actual seventh-height bad-degree theorem therefore receives every coordinate input from the physical chart. The original public theorem remains with exactly its previous hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-original-long-bad-degree-subpower"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalBadDegreeAverage.actual_long_bad_degree_subpower"),
                H("Derive the coordinate heights from the actual reduced basis"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For each epsilon>0 one positive C works for all primes p and actual reduced index-p-cubed and index-p-squared bases of the same original lattice parameters t,w and literal box X,Y. The first basis is long: p^6<H^2*Q(R), with positive H and H^2=XY. The original middle parameter lies in the box, the actual anchor satisfies physical(q)=(-w,-t), the basis first coordinate and original middle parameters are units modulo p^3, and the original right side 1+a1*a2*t*w is a unit. Every actual retained endpoint pair obeys the original word, has unit first physical coordinates, and lies in the literal box. Assuming 2X,2Y<p^3 and the three stated numerical cutoffs, its actual maximum derivative-zero degree is at most C*p^epsilon*(1+6H/(p*sqrt(Q(R2)))).")),
                    Paragraph(Text("Take sigma=sqrt(Q(R)) from the actual long reduced basis and define J1=8H/sigma and J2=4H*sigma/p^3. The existing reduced-basis coordinate bound proves the anchor and all endpoint height inputs. The long-scale theorem proves J2<=J1, J2>2 and J1*J2=32XY/p^3. Thus no height supplier is assumed. Consume actual_record_bad_degree_subpower with these actual inputs. The explicit inequalities (32XY/p^3)^5<=M^5*p^3, (10368*3^9)^5*M^35<p^4 and (24*(8*18)^4)^5*M^40<p remain hypotheses; they have not been discharged over the final original range."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-original-long-bad-degree-average-seventh"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalBadDegreeAverage.actual_long_bad_degree_average_seventh"),
                H("Average actual long-chart defects under seventh height"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Let A=XY. With the same original finite parameter domain, actual long prime-cube charts, endpoint word and units, physical boxes, 1<=X<=Y, 2Y<p^3, A<2p^4 and H>=p, the single scale condition seventhHeightConstant*(32A/p^3)^7<p^5 gives sum actualRecordBadDegree<=C*p^epsilon*[A+(A/p)*(1+log(2p)/log(2))+A^2/p^4]. Choose genuine reduced prime-square bases only at actual parameters and consume the existing physical-weight average. No counting or coordinate estimate is assumed. To retain the original three-cutoff interface, an actual parameter in a nonempty domain supplies long-scale bounds proving 1<=32A/p^3; when the domain is empty its sum is zero. This module does not claim the full arbitrary-modulus conjecture or literature priority."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-original-long-bad-degree-average"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalBadDegreeAverage.actual_long_bad_degree_average"),
                H("Average the actual maximum derivative defects"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Let A=XY. Under 1<=X<=Y, 2Y<p^3, A<2p^4, positive H with H^2=A and H>=p, and the same three numerical cutoffs, let s be any finite set of actual original unit middle parameters in the literal rectangle. An actual reduced long index-p-cubed basis matching R,V is required only at members of s. Keep the actual anchor, original coefficient units, unit basis first coordinate, original word, endpoint units and literal endpoint boxes, and the unit original right side at every such parameter. Then the sum of actualRecordBadDegree over s is at most C*p^epsilon*[A+(A/p)*(1+log(2p)/log(2))+A^2/p^4], with one constant chosen before p and all chart data.")),
                    Paragraph(Text("Map the original units to the prime-square quotient and choose a genuine reduced prime-square basis only at each parameter in s, defining the unused value outside s to be zero. The preceding long-chart theorem bounds each actual degree by its prime-square shortest-vector weight. Dominate 1+6H/(p*sigma) by six times 1+H/(p*sigma), then apply the existing actual_physical_weight_average to the same finite set of original parameters. There is no count, injection, height or weight estimate supplied as a hypothesis, and no impossible globally quantified basis witness at the zero parameter."))),
                DescribeRole.Theorem),
            Paragraph(Text("These are actual-chart bounds used to remove the derivative-defect term in the global retained count. The source problem and original numerical cutoffs are attributed to Pascadi. The numerical cutoffs and reconstruction of all original rows still require their own arguments; this module does not assert the full original conjecture or official acceptance.")))));
}
