using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class FiniteSourceScreeningDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual path gradients connect the finite counting Laplacian with the uniformly weighted node space.",
        H("Finite Source Screening"), Blocks(
            Def("Potential", "finitesourcescreening-potential", "A concrete potential assigns a real value to every original occurrence node, including the root and terminal nodes."),
            Def("rootNode", "finitesourcescreening-root-node", "The root is the reached empty address."),
            Def("nodeLp", "finitesourcescreening-node-lp", "A concrete potential is represented in the actual node L2 space with uniform mass 1/N(n)."),
            Def("child", "finitesourcescreening-child", "Each reached nonempty address identifies the child endpoint of one original edge."),
            Def("parent", "finitesourcescreening-parent", "Deleting the final direction gives the reached parent endpoint. Prefix closure supplies membership in the same source."),
            Def("gradient", "finitesourcescreening-gradient", "The gradient is parent value minus child value on every reached edge, extended by zero to all absent coordinates of the common real edge Hilbert space."),
            Def("Supported", "finitesourcescreening-supported", "An edge vector is supported when all coordinates outside the actual reached edge set vanish."),
            Def("reconstruct", "finitesourcescreening-reconstruct", "Reconstruction subtracts the root-to-node sum of edge coordinates from the prescribed root value."),
            Def("countingLaplacian", "finitesourcescreening-counting-laplacian", "The counting Laplacian sums the signed contributions of each original unit-conductance parent-child edge exactly once. The root has no killing term."),
            Def("nodeEquiv", "finitesourcescreening-node-equiv", "The uniform L2 representation is a continuous linear equivalence. Positive mass at every actual occurrence makes concrete potentials faithful, and every L2 element has a concrete representative."),
            Def("L", "finitesourcescreening-laplacian", "The actual counting Laplacian acts on NodeL2 by transport through the faithful concrete-potential equivalence."),
            Def("root", "finitesourcescreening-root", "Root evaluation is the continuous linear functional obtained from the actual empty-address coordinate."),
            Def("source", "finitesourcescreening-source", "The source is the counting root delta represented in uniform NodeL2; pairing with a concrete potential gives its root value divided by N(n)."),
            Describe.Lean(DescribeId.Create("finitesourcescreening-actual-reconstruction-energy"),
                DeclarationHandle.Create(Prefix + "actual_reconstruction_energy"),
                H("Actual reconstruction and energy"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Path sums telescope to the root value minus the node value. Conversely, every supported edge vector is recovered as the gradient of its reconstructed potential. Summing the signed edge contributions gives counting integration by parts; passing to uniform node measure introduces exactly the factor N(n). The reconstructed L2 potential is c times the constant one minus J(n)z. All assertions quantify over every natural source index, so empty edge sums are included."))), DescribeRole.Theorem),
            Def("unitInverse", "finitesourcescreening-unit-inverse", "For a complete real inner-product space, unitInverse attaches the inverse continuous linear map to an explicit IsUnit proof."),
            Describe.Lean(DescribeId.Create("finitesourcescreening-actual-screening-bridge"),
                DeclarationHandle.Create(Prefix + "actual_screening_bridge"),
                H("Actual node-space bridge"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every actual node-space potential decomposes into its root value and supported path increments. The transported counting Laplacian has the supported-edge bilinear energy with the exact factor N(n). Root evaluation and root-delta pairing give respectively c and c/N(n) on c times one minus J(n)z."))), DescribeRole.Theorem),
            Def("root_response", "finitesourcescreening-root-response", "For a positive screening parameter, root_response evaluates the actual root delta through the proved inverse of the counting Laplacian plus lambda."),
            Def("screened_inverse", "finitesourcescreening-screened-inverse", "For a positive screening parameter, screened_inverse is the proved inverse on the full common edge Hilbert space of I plus N(n) times lambda times the centered finite covariance."),
            Describe.Lean(DescribeId.Create("finitesourcescreening-finite-source-screening"),
                DeclarationHandle.Create(Prefix + "finite_source_screening"),
                H("Centered counting response"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every natural source index n and positive lambda, the counting root response minus 1/(N(n) lambda) equals the inner product of v(n) with its image under the full common-edge inverse of I plus N(n) lambda Sigma(n). The root value and the path-gradient energy establish the original counting weak equation. This gives the exact constant-mode subtraction, including the edge-free sources at n=0 and n=1."))), DescribeRole.Theorem),
            Paragraph(Text("The source node spaces depend on n, while the edge space is common to all sources. Counting energy is unnormalized, node inner products use uniform mass 1/N(n), and all original edges have unit conductance. Positive screening gives a genuine inverse on the node space and on the full common edge space, including absent coordinates.")))));

    private static DocumentBlock Def(string name, string id, string prose) => Describe.Lean(
        DescribeId.Create(id),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
