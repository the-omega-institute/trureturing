using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeCosetOperatorCorrectionDocument : IScribeDocumentDefinition
{
    private static DocumentBlock D(string selector, string text) => Describe.Lean(
        DescribeId.Create("coset-operatorcorrection-" + selector.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeCosetOperatorCorrection." + selector),
        H(selector), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeCosetOperatorCorrection", H("All-state intermediate-projection correction"), Blocks(
            D("inner_creation_expansion", "For every positive definite original lattice D, arbitrary finite external rank, integral B, symmetric even-diagonal C, integral external charges a,d, every original source u and target g and integer mode m, the full native ambient mode of Y(J(a,u)) on J(d,g) is the finite natural-index sum of mixedState in sector a+d with the j-th native external creation coefficient and compressed(a,d,u,m+j,g). The charged base is ground_reconstruction. The native multiplication_recursion and compressed_multiplication_recursion extend it through every source polynomial; native truncation justifies the two normal-product coefficient sums. No ambient positivity is assumed, and both ranks may be zero."),
            D("intermediate_projection_correction", "For every positive definite original lattice D, arbitrary finite external rank, integral B, symmetric even-diagonal C, every integral external charges a,b,c, all original states u,v,w and integer modes p,q, the theorem delivers both finite support of the exact correction summand and the following full equation: projection in sector a+b+c of the actual nested mode Y(J(a,u))[p](Y(J(b,v))[q]J(c,w)) equals the finite natural-index sum over j of correction(a,b,j) times compressed(a,b+c,u,p-j,compressed(b,c,v,q+j,w)). Here correction is exactly (-1)^j times the rational generalized binomial choose(schur(a,b),j), cast to complex scalars. The inner coefficient is reconstructed first. The all-state projected transverse polynomial action and transverse_creation_coefficient identify each outer term. The inner truncation alone makes the entire summand support finite; no uniform outer lower bound is imposed. The original epsilon and half diagonal remain literal, and no positivity or nondegeneracy of the ambient block lattice is assumed."),
            Paragraph(Text("The oscillator separation and normal-ordering method uses native lattice fields with the convention of Bakalov-Kac, math/0402315v1, section 4.1. It is an exact operator identity on the original finite-charge carrier. It does not assert a new VOA structure, physical realization, phase descent or completion of a string-theoretic correspondence.")))));
}
