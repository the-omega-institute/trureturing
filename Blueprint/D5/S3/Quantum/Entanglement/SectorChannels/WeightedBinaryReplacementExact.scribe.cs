using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SectorChannels;

internal sealed class WeightedBinaryReplacementExactDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed pure two-qubit resource serving a matched binary replacement has a piecewise exact error. Matching the target mass, not increasing entanglement alone, governs this zero-communication task.",
        H("Exact weighted binary replacement"),
        Blocks(Describe.Lean(
            DescribeId.Create("weighted-binary-replacement-exact"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Entanglement/SectorChannels/WeightedBinaryReplacementExact.result"),
            H("The exact diamond error over arbitrary local channels"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The resource is the normalized pure vector a|00>+b|11>, with 0<b<=a. Write q=b^2. The target is diagonal with weights (w,0,0,1-w), where 0<=w<=1/2. There is neither communication nor an additional shared random draw.")),
                Paragraph(Text(
                    "If w<=q, set v=max(w/q,1-w/q). The exact unhalved diamond distance is 4q(sqrt(v)-v). If w>q, it is 2(w-(a+b-sqrt(1-w))^2). The theorem constructs native trace-preserving completely positive maps attaining the formula and bounds every allowed pair of local channels. The lower bound even holds for a joint competitor constrained only on one basis input.")),
                Paragraph(Text(
                    "Extract the binary effects as principal blocks of the amplified matrix-unit action, and absorb square roots of the Schmidt amplitudes. Averaging the two effects increases both diagonal hits. For one resulting matrix H between zero and D=diag(a,b), let L=tr(DH) and U=tr(H). Nonnegativity of the determinants of H and D-H gives two scalar upper bounds on tr(H^2). In the middle range they meet at U=(L+ab)/(a+b). For small L the optimum is a filter on the smaller Schmidt direction; large L follows by taking the complement.")),
                Paragraph(Text(
                    "The three arcs have explicit physical attainers: filtering on the smaller direction or a rank-one projector and its complement. Clipping their diagonal hits by the target masses gives the exact error. The optimal output channel is a replacer; reference stabilization does not change its trace-norm distance to the target.")),
                Paragraph(Text(
                    "This is a fixed-resource, matched-diagonal replacement result. It does not assert an optimum for general coherent input-dependent recovery, mixed resources, shared randomness, or communications.")))))));
}
