using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiIntervalAutocorrelationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal integer interval autocorrelations retain residue multiplicities and give the six-letter central comparison with factor 64.",
        H("Actual interval weights and central counts"),
        Blocks(
            Paragraph(Text("Let G be a finite group, and let u and v be homomorphisms from the additive integers, written multiplicatively, into G. The interval measure sums one group-algebra atom for every integer in [-N,N]. Equal images remain separate summands; no injectivity or interval shorter than the group order is assumed. The normalized autocorrelation divides by 2N+1.")),
            Describe.Lean(DescribeId.Create("literal-integer-interval-triangular-autocorrelation"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiIntervalAutocorrelation.integerInterval_autocorrelation_coeff"),
                H("The exact triangular weights"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual autocorrelation coefficient is the sum over integers |n|<=2N of (2N+1-|n|) times the coefficient of the atom at u(n). This sums every residue collision with its full integer multiplicity.")),
                    Paragraph(Text("Expand the two interval sums and group pairs (a,b) by their integer difference n=a-b. The difference fiber is in explicit bijection with the intersection of two integer intervals, whose cardinality is 2N+1-|n|. This is an integer fiber count, not a count of distinct group images."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-integer-fejer-coefficient-sandwich"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiIntervalAutocorrelation.integerIntervalFejer_sandwich"),
                H("The coefficient sandwich"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Coefficient by coefficient, the original interval measure is at most twice its normalized autocorrelation, and the normalized autocorrelation is at most the measure on [-2N,2N]. The normalized triangular weight lies in [0,1] on its support and is at least 1/2 on [-N,N]. The argument sums these inequalities before identifying any equal images."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-alternating-interval-center-count-comparison"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiIntervalAutocorrelation.alternating_integer_interval_center_le"),
                H("Six alternating interval letters at a central element"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any central z in G, the coefficient at z of (mu_u,N times mu_v,M)^3 is at most 64 times the identity coefficient of (mu_u,2N times mu_v,2M)^3. N and M are separate nonnegative integer widths. No symmetry or positivity of the nonsymmetric product itself is assumed.")),
                    Paragraph(Text("The lower sandwich and actual convolution monotonicity contribute the six factors of 2. The central autocorrelation theorem applies to the normalized actual factors. The upper sandwich then removes all triangular weights in the doubled intervals. The group-algebra anti-involution and Gram factor are constructed in CentralAutocorrelation; there is no assumed center-bound or positive-operator supplier."))),
                DescribeRole.Theorem),
            Paragraph(Text("This general interval result does not by itself identify a matrix word with its coefficient. PascadiScalarCenters supplies the exact upper/lower unipotent word, its overall sign, the row permutation, the scalar centrality proof, and the natural-floor interpretation for real widths.")))));
}
