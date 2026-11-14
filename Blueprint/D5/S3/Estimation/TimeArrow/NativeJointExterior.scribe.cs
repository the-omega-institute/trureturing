using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class NativeJointExteriorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint exterior independence in the compensated native finite path.",
        H("A marked edge and its entire joint exterior"),
        Blocks(Describe.Lean(
            DescribeId.Create("native-marked-joint-exterior"),
            DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeJointExterior.native_marked_joint_exterior"),
            H("The exact finite exterior cylinder law"),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Fix a deterministic true support S with exactly q elements, where 1 <= q < M. Let 0 < r < 1 and let the original compensation rq/(M-q) be less than one. The vertex carrier, transition and uniform-start complete-path probability are those of FiniteSupportSelectionBayes. Write n=2M. There is no independent replacement process.")),
                Paragraph(Text("A path has s=a+1+b edges and the central edge has time a. The exterior is the single joint tuple of all vertices at times at most a-2 and at least a+3. Its two parts may be tested together in an arbitrary cylinder. For a signal row i in S and a sign sigma in {1,-1}, the joint mass of that cylinder and the central event X_a=inl(i), chi(X_(a+1))=sigma equals (1+sigma*r)/(2n) times the mass of the entire exterior cylinder.")),
                Paragraph(Text("The cylinderMass definition sums the actual probability over every complete native observation satisfying both exterior and central constraints. Splitting each complete history at its central edge is bijective. The compensated profile has zero sum, and its parity-weighted sum is also zero; composing two original transition kernels gives the uniform kernel. Summing the one omitted connecting vertex on each side therefore makes both endpoint fiber masses constant. Their product factors the complete joint exterior law, including simultaneous observation of the distant past and future.")),
                Paragraph(Text("All a,b>=0 are included. At either end, an empty exterior is the unique empty tuple; with one adjacent edge, the original column or row normalization replaces the two-step calculation. Thus the first two and last two central positions and the one-edge path are included. A zero-edge path has no central edge. The identity uses no conditional division and remains valid for exterior cylinders of mass zero.")),
                Paragraph(Text("Any marked edge at time-distance at least three is a function of the recorded exterior tuple. The result supplies the native joint dependence input for such marks. It does not supply a Chen-Stein process comparison, a product-Poisson law, a total-variation estimate, the local second-moment constants, or the full signal-vector approximation. The probability of a signal sign is (1+sigma*r)/(2n); at observation scale L=s/n its count mean is L*(1+sigma*r)/2."))),
            DescribeRole.Theorem))));
}
