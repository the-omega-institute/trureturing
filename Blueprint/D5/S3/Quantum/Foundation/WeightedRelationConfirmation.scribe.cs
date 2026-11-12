using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class WeightedRelationConfirmationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attained weighted mixed-state confirmation gap.",
        H("Attained weighted mixed-state confirmation gap"),
        Blocks(
            Paragraph(Text("Use the same closed generating original cone, strictly positive unit, full normalized base, full pure set P and full proper interval. The entire finite P is bijectively indexed by L disjoint-union R disjoint-union Z. The normalized unique relation has strictly positive left weights alpha and right weights beta, each of total mass one. All Z vertices have zero relation coefficient and remain in the original carrier. The relation nullity is one; no extension from a selected subconfiguration is assumed.")),
            Describe.Lean(DescribeId.Create("relationvector"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/WeightedRelationConfirmation.relationVector"),
                H("A full signed relation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("On the three disjoint label groups the coefficients are alpha(i), minus beta(j), and zero. In particular every zero-coefficient original pure vertex is retained."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("relation-effect"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/WeightedRelationConfirmation.relation_effect"),
                H("Bounded balanced assignments descend"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For any assignment v to every label in the full bijection, bounds 0<=v<=1 and equality of the alpha-weighted left and beta-weighted right readings imply existence of an original proper real linear effect realizing all those values. The premise that the displayed relation spans the entire kernel is used here; for the attained-gap theorem it is derived from original nullity one and the actual normalized vector relation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("barycenter"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/WeightedRelationConfirmation.barycenter"),
                H("The source weighted barycenter"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For any finite group J of original pure labels, barycenter is the sum of beta(j)b_j over J divided by its total beta mass. A group containing several vertices is retained as that mixed source barycenter."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("partition-gap"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/WeightedRelationConfirmation.partitionGap"),
                H("The complete source gap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For specified p and J this predicate states membership of both source weighted barycenters in the original base, comparison values zero at each, the exact positive midpoint value t/(2 max(b,1-b)), and actual original proper confirming effects attaining all three values."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exchange"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/WeightedRelationConfirmation.exchange"),
                H("Exchange only the relation sides"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The full pure-point indexing bijection exchanges its left and right nonzero groups and retains the same complete zero-coefficient group."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weighted-gap-after-exchange"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/WeightedRelationConfirmation.weighted_gap_after_exchange"),
                H("Exact attained original values"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("There exists a label whose positive weight is globally minimal among all alpha and beta weights. If it is a right label, the theorem exchanges the two sides and retains every free vertex. Orient that label as the left p and put t equal to its weight. For every J with J and its complement in the entire right label set both nonempty, put b=sum over J of beta, x=barycenter(J), and y=barycenter(complement J). Then x and y belong to the original K, T_p(x)=T_p(y)=0, and T_p((x+y)/2)=t/(2 max(b,1-b))>0. The theorem also supplies original confirming proper effects attaining each of these three values. All quantifiers retain arbitrary positive weights, arbitrary such J and arbitrary finite Z, including empty Z."))), DescribeRole.Theorem))));
}
