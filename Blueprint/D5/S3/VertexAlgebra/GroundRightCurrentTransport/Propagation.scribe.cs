using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GroundRightCurrentTransport;

internal sealed class PropagationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/GroundRightCurrentTransport/Propagation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Negative right-source compatibility propagation",
        H("Negative right-source compatibility propagation"),
        Blocks(
            Paragraph(Text("OriginalCompatible is the full three-supported coefficient law on the exact original source mu and actual correctedField. Its parameters gamma and delta are arbitrary integers; p,q,r and actual x are universally quantified. The left slice uses gamma+delta without parity reduction. In odd-odd sectors this sum is 2, whose conversion to lift 0 increases the physical mode by one; the carry is retained, not removed by an integer-binomial replacement.")),
            Paragraph(Text("The inverse/full-law bridge uses the Hahn tail of the actual original Y(a)b and independently certified physical locality. OriginalCompatible implies zero defect by finite inversion. Zero defect implies every signed compatibility coefficient by the supported recurrence. These are proof steps, not premises on the target module.")),
            Paragraph(Text("The source zero mode sends projectedGround(alpha,epsilon) to bilinear(unitCharge(i),alpha) times projectedGround(alpha,not epsilon). This formula includes the zero-charge coefficient and never divides by it. Therefore compatibility at both smaller projected signs suffices for the actual h0 correction.")),
            Paragraph(Text("Negative-current propagation consumes the unconditional native defect transport, kills its two smaller defects, and recovers the entire signed coefficient law. The original second source b and actual input x are unrestricted. The word theorem iterates actual source neutral modes with negative indices -(j.2+1).")),
            Paragraph(Text("The word theorem assumes the displayed exact full ground-pair compatibility for every pair of charges, both projected signs and every lift. That ground-pair base remains unproved here. Arbitrary-first transport and the complete Moonshine, VOA, CFT, anomaly, fusion, string and AdS/CFT programme remain open. These are repository-derived consequences of classical twisted-lattice calculus; no literature novelty or physical realization is claimed.")),
            Describe.Lean(
                DescribeId.Create("ground-right-native-compatible-defect"),
                DeclarationHandle.Create(Prefix + "compatible_defect"),
                H("Full law implies zero defect"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original full three-supported coefficient law implies vanishing of each native defect, by the source tail and finite inverse residue transform."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ground-right-native-defect-compatible"),
                DeclarationHandle.Create(Prefix + "defect_compatible"),
                H("Zero defects recover the full law"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Vanishing of all signed native defects recovers every p,q,r coefficient, all three finite-support clauses and both ordered terms of the original law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ground-right-native-compatible-smul-left"),
                DeclarationHandle.Create(Prefix + "compatible_smul_left"),
                H("Scalar multiplication of the first source"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("OriginalCompatible is preserved by every complex scalar in its first source, with its original supports transported by scalar multiplication."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ground-right-native-ground-zero-mode"),
                DeclarationHandle.Create(Prefix + "ground_zero_mode"),
                H("Exact projected ground zero mode"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original neutral zero mode multiplies by the bilinear charge coefficient and reverses the projected ground sign. Zero charge is included and the coefficient is never divided out."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ground-right-native-projectedground-negative-current-step"),
                DeclarationHandle.Create(Prefix + "projectedGround_negative_current_step"),
                H("Full negative-current compatibility step"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive natural m and current i, compatibility of the smaller original b at both projected signs and all lifts implies OriginalCompatible(projectedGround(alpha,epsilon),neutralMode(i,-m,b),gamma,delta), for arbitrary epsilon, gamma and delta."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ground-right-native-projectedground-right-word"),
                DeclarationHandle.Create(Prefix + "projectedGround_right_word"),
                H("Conditional full right-word propagation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assuming only exact all-charge, both-sign ground-pair OriginalCompatible at every lift, the same full signed law holds with the second projected ground source replaced by any finite word of actual negative source currents."))),
                DescribeRole.Theorem))));
}
