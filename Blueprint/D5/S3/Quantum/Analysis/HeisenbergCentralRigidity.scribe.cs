using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class HeisenbergCentralRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual complex compact smooth Heisenberg graph has a single-valued closed gradient and a central derivative with zero kernel on the whole space.",
        H("Central Rigidity of the Whole Heisenberg Graph"),
        Blocks(Describe.Lean(
            DescribeId.Create("heisenberg-central-rigidity"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/HeisenbergCentralRigidity.central_rigidity"),
            H("Joint closure, complex weak central differentiation and whole-line rigidity"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The coordinate space is EuclideanSpace Real (Fin 3), identified with triples (x,y,z). Its measure is raw Lebesgue volume, and State is the complex L2 space for this measure. The frame consists, in order, of U = partial_x - (y/2) partial_z, V = partial_y + (x/2) partial_z, and Z = partial_z. The derivatives are real directional derivatives of complex functions.")),
                Paragraph(Text("compactCore consists of precisely the compactly supported complex Schwartz functions. Every complex smooth compactly supported function gives such a Schwartz function through HasCompactSupport.toSchwartzMap, with the same values and derivatives. coreJet records its L2 state together with all three L2 field derivatives. jointGraph is the topological closure of the range of this one linear map in the product of the state space and the three component spaces. Thus one approximating function supplies all four coordinates simultaneously. No component is discarded and no replacement by isotropic Euclidean H1 is made.")),
                Paragraph(Text("The compact-core state projection is dense. Its joint gradient coreOperator is closable, and the graph of its Mathlib partial-linear-map closure closedOperator equals jointGraph. Two members of this graph with the same state have identical triples of components. The existence of the closure constructor alone is insufficient: the proof establishes the absence of nonzero vertical graph vectors, using the injective continuous embedding of L2 into tempered distributions and the three distributional field equations.")),
                Paragraph(Text("For every graph member (u,g) and every complex smooth compactly supported eta, the integral of g_Z times conjugate eta equals minus the integral of u times conjugate partial_z eta. The quantifiers include zero states, arbitrary angular dependence and unbounded state support. L2 pairing makes both integrals finite. This identifies the actual closed central component as the distributional central derivative.")),
                Paragraph(Text("For every member of this actual graph, g_Z = 0 if and only if u = 0 in L2. For the forward direction, the distributional Fourier derivative formula forces the central-frequency coordinate times the L2 Fourier transform to vanish as a distribution. Multiplication by that coordinate preserves local integrability, so compact-test separation makes the product vanish almost everywhere. The central-frequency hyperplane is a proper real linear subspace and has Lebesgue measure zero. The entire Fourier transform therefore vanishes in L2, and Fourier inversion gives u = 0. The reverse direction follows from the already established single-valued graph. This treats the zero-frequency hyperplane and all spatial tails without imposing compact support on u or restricting its angular modes.")),
                Paragraph(Text("Mathlib uses the Fourier character exp(-2*pi*i*inner(x,xi)), whereas the source central partial Fourier convention uses exp(-i*k*z). The distributional multiplier in this proof is consequently 2*pi*i*xi_z, and k = 2*pi*xi_z. Its nonzero scalar factor is removed explicitly. The proof uses the full L2 Fourier isometry and requires no L1 hypothesis or one-dimensional Fourier identification.")),
                Paragraph(Text("For the source's Corollary 11.2, the kernel conclusion supplies positive central energy for a nonzero member of the original H1 graph. The separate horizontal full-Green bound, the positive finite full-clock Green denominator, the sharp infimum and optimal coefficient remain additional obligations. Only together with their respective proofs can these imply the original strict inequality and nonattainment. This result provides no positive uniform spectral gap, minimizing profile, physical realization, response rank, spatial dimension or higher-contact conclusion."))),
            DescribeRole.Theorem))));
}
