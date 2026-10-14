using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TransverseMetric;

internal sealed class RealAdaptedFrameDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real original adapted frames and native positivity",
        H("Real original adapted frames and native positivity"),
        Blocks(
            Paragraph(Text("The inputs are the original integral lattice Gram, both complex inverse-Gram equations, a nonzero original integral charge, rank at least two, and actual positive-minus-negative signature equal to rank minus two. Taking real parts proves both real inverse equations without assuming the complex inverse is real. Nondegeneracy removes the quadratic radical; inertia then gives one negative and rank minus one positive directions. A real orthogonal quadratic basis and the positive square root of an opposite-sign norm ratio give two null vectors whose sum detects any nonzero functional. The original charge functional therefore detects a real null direction.")),
            Paragraph(Text("The partner is exactly the original adaptedPartner: chosenP inverse times the unchanged charge, minus chosenH times chosenP inverse squared times the null direction. Its original pairing, nullity, charge decomposition and original chargeQuadratic mass-shell normalization are retained. The generic real HyperbolicFrame extension supplies real rows, a real two-sided inverse, distinct axes and literal duals. Complexification proves both complex inverse equations, every star-fixed row and both original complex dual equations. No real frame, null separator, orthogonal-complement positivity or coordinate isometry is supplied as an input.")),
            Paragraph(Text("The constructed rows are consumed by LorentzianSignature.transverseGram_posDef, nativePolynomial_positive_of_lorentzian and native_degree_one_negative_C0_positive_of_lorentzian. The resulting frame carries literal transverse Gram positivity, strict real norm for every nonzero native polynomial, and positivity of the original negative right-C0 pairing on every nonzero original native J-eigenvalue-one state at any integer level. There is no separately supplied star-fixed-frame premise. Rank two is included with empty transverse axes. These are native-state results, not physical quotient positivity, global no-ghost, a neutral-charge result, beta-zero positivity, complete string theory or AdS/CFT.")),
            Describe.Lean(
                DescribeId.Create("real-adapted-frame-embed"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/RealAdaptedFrame.embed"),
                H("Literal real-to-complex coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The embedding casts each original ambient real coordinate to Complex without changing its index or normalization."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("real-adapted-frame-nativeframe"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/RealAdaptedFrame.NativeFrame"),
                H("Constructed real frame with original native consumers"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This output type records the real and complex inverse and dual laws, actual original partner and mass-shell identities, literal Gram positivity and both native positivity consumers. It is not assumed to be inhabited."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("real-adapted-frame-exists-native-frame"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/RealAdaptedFrame.exists_native_frame"),
                H("Nonzero original charges construct native positive real frames"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The theorem constructs an inhabitant from the original hypotheses. The substantive new step is real null separation from actual Lorentzian inertia and nondegeneracy, followed by the unchanged adaptedPartner and a real generic-field frame extension. The registered source readout is the original charge occurrence in the conclusion, with the full original hypothesis telescope retained. Replacing this charge by zero makes the frame impossible because chosenP vanishes, whereas the actual nonzero charge in an explicit integral hyperbolic plane satisfies the original theorem. The actual readout distinguishes zero and nonzero charges without an artificial enable bit."))), DescribeRole.Theorem))));
}
