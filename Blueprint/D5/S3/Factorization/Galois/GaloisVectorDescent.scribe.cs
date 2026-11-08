using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class GaloisVectorDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Effective descent for semilinear Galois vector spaces.", H("Effective descent for semilinear Galois vector spaces."),
        Blocks(
            Paragraph(Text("The invariant-generation method follows Qiuzhen-CFSG/CFSG, Theory/Representation/FiniteFieldSemilinearDisplacement/Descent.lean, revision 0c6635528a02dd46f2e93e2ade0c4ac647ad1eb7, Apache-2.0. The formulation with independent group, base-field, extension-field and carrier universes and the canonical tensor equivalence are the formal integration here. Basis extraction and base change use Mathlib. This is classical semilinear descent, with no claim of a new descent theorem.")),
            Describe.Lean(DescribeId.Create("galoisvectordescent-span-fixedpoints"), DeclarationHandle.Create("D5/S3/Factorization/Galois/GaloisVectorDescent.span_fixedPoints"), H("span fixedPoints"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The fixed vectors span over the extension field. Twisted orbit sums are fixed, so a linear form vanishing on the fixed vectors gives a relation among distinct field automorphisms. Artin independence makes that form zero. No division by the group order or finite-dimensionality is required."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("galoisvectordescent-exists-invariant-basis"), DeclarationHandle.Create("D5/S3/Factorization/Galois/GaloisVectorDescent.exists_invariant_basis"), H("exists invariant basis"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Extracting a basis from the spanning fixed vectors gives a basis fixed pointwise by the group; its index type lies in the carrier universe."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("galoisvectordescent-descentequiv"), DeclarationHandle.Create("D5/S3/Factorization/Galois/GaloisVectorDescent.descentEquiv"), H("descentEquiv"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The canonical map sends a tensor a tensor w to a times w. In invariant-basis coordinates the fixed vectors have coefficients in the fixed field, so base change gives an equivalence. The forward map is the canonical base-change map, independent of the basis used to prove bijectivity."))), DescribeRole.Definition))));
}
