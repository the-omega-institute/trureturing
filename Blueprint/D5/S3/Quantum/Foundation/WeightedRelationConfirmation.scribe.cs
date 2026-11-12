using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class WeightedRelationConfirmationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attained weighted mixed-state confirmation gap.",
        H("Attained weighted mixed-state confirmation gap"),
        Blocks(
            Paragraph(Text("Use the same closed generating original cone, strictly positive unit, full normalized base, full pure set P and full proper interval. The entire finite P is bijectively indexed by L disjoint-union R disjoint-union Z. The normalized unique relation has strictly positive left weights alpha and right weights beta, each of total mass one. All Z vertices have zero relation coefficient and remain in the original carrier. The relation nullity is one; no extension from a selected subconfiguration is assumed.")),
            Describe.Lean(DescribeId.Create("coordinates"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/WeightedRelationConfirmation.coordinates"),
                H("The full pure coordinate map"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every real coefficient function w on all of P, Phi(w)=sum_p w(p)p. No subset of pure points replaces this domain."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zerogluing"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/WeightedRelationConfirmation.zeroGluing"),
                H("Mixed-state zero gluing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every original pure p and all x,y in the entire original base K, if an original proper confirmer of p vanishes at x and another original proper confirmer vanishes at y, there exists an original proper confirmer vanishing at (x+y)/2. The two antecedent witnesses may differ. Existence of an excluding effect, rather than only a zero infimum, is the definition."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("coordinates-surjective"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/WeightedRelationConfirmation.coordinates_surjective"),
                H("Surjectivity on the original carrier"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Closedness, strict positivity and generatingness imply that Phi is onto A. Compactness of the original base and pure spanning are derived from the existing cone lemmas."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-effect-iff"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/WeightedRelationConfirmation.full_effect_iff"),
                H("The entire original proper interval"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every assignment v:P to R, there exists a unique original real linear effect f, proper on all of C and satisfying f(p)=v(p) at every original pure point, if and only if every v(p) belongs to [0,1] and sum_p w(p)v(p)=0 for every w in the entire kernel of Phi. Both the values and their complements extend nonnegatively to the entire original cone. Uniqueness follows from surjectivity of Phi."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("relation-sum-zero"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/WeightedRelationConfirmation.relation_sum_zero"),
                H("Relations have zero total coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every full pure coefficient vector w with Phi(w)=0, sum_p w(p)=0. This follows by applying the same original unit, whose value is one on every pure point."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("attained-comparison"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/WeightedRelationConfirmation.attained_comparison"),
                H("A universal lower bound with attainment"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every original cone vector x and reference p, if an original proper confirmer f of p satisfies f(x)<=g(x) for every original proper confirmer g of p, then T_p(x)=f(x). The proof uses the actual infimum defining the original comparison. No attainment assumption is made for unrelated minimization problems."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("no-single-positive"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/WeightedRelationConfirmation.no_single_positive"),
                H("No single extreme point on a relation side"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every full pure coefficient vector w with Phi(w)=0, if w(q)>0 and every other coefficient is nonpositive, there is a contradiction. The negative side expresses q as a convex combination of other original base points, contrary to its native extremality. The normalized gap theorem uses this to prove at least two vertices on both relation sides; the native one-relation obstruction uses it to construct actual alternate excluding effects."))), DescribeRole.Theorem),
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
                    Paragraph(Text("Both nonzero relation sides have at least two original pure vertices. There exists a label whose positive weight is globally minimal among all alpha and beta weights. If it is a right label, the theorem exchanges the two sides and retains every free vertex. Orient that label as the left p and put t equal to its weight. For every J with J and its complement in the entire right label set both nonempty, put b=sum over J of beta, x=barycenter(J), and y=barycenter(complement J). Then x and y belong to the original K, T_p(x)=T_p(y)=0, and T_p((x+y)/2)=t/(2 max(b,1-b))>0. The theorem also supplies original confirming proper effects attaining each of these three values. All quantifiers retain arbitrary positive weights, arbitrary such J and arbitrary finite Z, including empty Z."))), DescribeRole.Theorem))));
}
