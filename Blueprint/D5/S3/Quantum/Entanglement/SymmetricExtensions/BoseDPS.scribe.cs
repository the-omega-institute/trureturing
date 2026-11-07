using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SymmetricExtensions;

internal sealed class BoseDPSDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bose adaptation and closedness of actual DPS cones", H("Bose adaptation and closedness of actual DPS cones"),
        Blocks(
            Paragraph(Text("Britz-Laurent equations (25)-(31) use a Bose leaf-projector sandwich, unnormalized partial trace, and leaf cuts. The definitions here quantify all leaf subsets, with exact equivalences to the ordinary prefix and adapted half-prefix conventions. Complementary cuts account for the root. The support argument is due to Hansenne-Xu-Kraft-Guehne; the equality application note has byline Haobo Ma then Wenlin Zhang.")),
            Describe.Lean(DescribeId.Create("bosedps-ordinarywitness"),
                DeclarationHandle.Create(Prefix + "OrdinaryWitness"),
                H("OrdinaryWitness"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One actual root-leaf marginal is prescribed; the leaf-projector sandwich and positivity at every leaf-only cut are imposed. The empty cut supplies ordinary positivity."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bosedps-adaptedwitness"),
                DeclarationHandle.Create(Prefix + "AdaptedWitness"),
                H("AdaptedWitness"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The witness is supported by the full symmetric projector, has the prescribed ordered marginal, and is positive at every cut, including both endpoints."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bosedps-ordinarydps"),
                DeclarationHandle.Create(Prefix + "ordinaryDPS"),
                H("ordinaryDPS"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the set of inputs possessing the actual ordinary tensor witness. No trace normalization is imposed."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bosedps-adapteddps"),
                DeclarationHandle.Create(Prefix + "adaptedDPS"),
                H("adaptedDPS"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the set of inputs possessing the actual full-Bose tensor witness. No trace normalization is imposed."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bosedps-adapted-iff-ordinary"),
                DeclarationHandle.Create(Prefix + "adapted_iff_ordinary"),
                H("adapted iff ordinary"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any pair-Bose-supported input, the ordinary and adapted predicates select the same individual E. Complementary cuts account for cuts containing the root. Zero and singular matrices remain in scope."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bosedps-adapted-eq-inter"),
                DeclarationHandle.Create(Prefix + "adapted_eq_inter"),
                H("adapted eq inter"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual adapted cone equals the ordinary cone intersected with the positive symmetric-support face, for arbitrary finite register and local-label types with two distinct selected registers."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bosedps-ordinary-closed"),
                DeclarationHandle.Create(Prefix + "ordinary_closed"),
                H("ordinary closed"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a convergent sequence of inputs, every positive lift has trace equal to its input trace. The existing PSD entry bound therefore bounds the lifts. A convergent lift subsequence preserves the leaf sandwich, prescribed marginal, and every cut inequality, proving closedness of the projected cone."))),
                DescribeRole.Theorem),
            Paragraph(Text("For the ordinary witness, permutations fixing the root carry any two leaf cuts of equal cardinality to one another. The leaf-projector sandwich supplies the required conjugation invariance, and positive semidefiniteness transports through the corresponding computational-basis submatrix.")),
            Paragraph(Text("For registers 0 through t with root 0, choosing k equal to the cardinality of a leaf cut identifies every leaf-only positivity condition with the first k leaves. The prescribed ordered marginal and the unnormalized scale are unchanged.")),
            Paragraph(Text("For a full Bose-supported positive operator, arbitrary register permutations carry cuts of equal cardinality, including cuts containing the root. The complementary-cut transpose reduces the remaining cuts to the first k leaves for k at most floor((t+1)/2), while empty and full cuts remain explicit.")),
            Paragraph(Text("These cardinality transports are the complete ordinary and adapted DPS prefix conventions used by the application; they retain zero and singular matrices and impose no trace normalization.")))));
}
