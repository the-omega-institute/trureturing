using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class FinitePureEffectDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full finite pure coordinates and original effects.",
        H("Full finite pure coordinates and original effects"),
        Blocks(
            Paragraph(Text("The carrier A is a finite dimensional real normed space. The cone C is closed, contains zero, is closed under addition and nonnegative real scaling, and spans all of A. The linear unit u is strictly positive on every nonzero vector of C. The set P is exactly the extreme points of the entire base K={x in C : u(x)=1}; its finiteness is an explicit additional hypothesis. All real linear functionals proper on the entire C remain in the effect interval.")),
            Describe.Lean(DescribeId.Create("coordinates"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FinitePureEffectDescent.coordinates"),
                H("The full pure coordinate map"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every real coefficient function w on all of P, Phi(w)=sum_p w(p)p. No subset of pure points replaces this domain."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zerogluing"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FinitePureEffectDescent.zeroGluing"),
                H("Mixed-state zero gluing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every original pure p and all x,y in the entire original base K, if an original proper confirmer of p vanishes at x and another original proper confirmer vanishes at y, there exists an original proper confirmer vanishing at (x+y)/2. The two antecedent witnesses may differ. Existence of an excluding effect, rather than only a zero infimum, is the definition."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("coordinates-surjective"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FinitePureEffectDescent.coordinates_surjective"),
                H("Surjectivity on the original carrier"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Closedness, strict positivity and generatingness imply that Phi is onto A. Compactness of the original base and pure spanning are derived from the existing cone lemmas."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-effect-iff"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FinitePureEffectDescent.full_effect_iff"),
                H("The entire original proper interval"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every assignment v:P to R, there exists a unique original real linear effect f, proper on all of C and satisfying f(p)=v(p) at every original pure point, if and only if every v(p) belongs to [0,1] and sum_p w(p)v(p)=0 for every w in the entire kernel of Phi. Both the values and their complements extend nonnegatively to the entire original cone. Uniqueness follows from surjectivity of Phi."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("relation-sum-zero"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FinitePureEffectDescent.relation_sum_zero"),
                H("Relations have zero total coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every full pure coefficient vector w with Phi(w)=0, sum_p w(p)=0. This follows by applying the same original unit, whose value is one on every pure point."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("attained-comparison"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FinitePureEffectDescent.attained_comparison"),
                H("A universal lower bound with attainment"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every original cone vector x and reference p, if an original proper confirmer f of p satisfies f(x)<=g(x) for every original proper confirmer g of p, then T_p(x)=f(x). The proof uses the actual infimum defining the original comparison. No attainment assumption is made for unrelated minimization problems."))), DescribeRole.Theorem))));
}
