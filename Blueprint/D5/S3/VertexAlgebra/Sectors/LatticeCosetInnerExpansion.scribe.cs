using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeCosetInnerExpansionDocument : IScribeDocumentDefinition
{
    private static DocumentBlock D(string selector, string text, DescribeRole role) => Describe.Lean(
        DescribeId.Create("coset-inner-expansion-" + selector.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeCosetInnerExpansion." + selector),
        H(selector), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeCosetInnerExpansion", H("Native compressed source recursion"), Blocks(
            D("compressedField", "For arbitrary original lattice D, arbitrary finite external rank, integral B, symmetric even-diagonal C, external integral source and target charges a,d and every original state u, compressedField is the literal native ambient Y of J(a,u), composed with the target injection J(d) and output projection P(a+d). Its coefficient at integer mode m is the existing compressed coefficient. Native statewise Laurent truncation supplies its vertex-operator bound; no new graded cutoff or ambient positivity is assumed.", DescribeRole.Definition),
            D("compressed_multiplication_recursion", "For every positive definite original D, arbitrary finite external rank, integral B, symmetric even-diagonal C, integral external charges a,d, old oscillator index x, old integral source charge n and arbitrary old source polynomial f, the compressedField of single(n,X(x) f) equals normalMinusOne of the x-th divided derivative of the native integral shifted current in target sector d and compressedField of single(n,f). All original epsilon factors and integral zero-mode exponents remain in the compressedField. Negative current modes are independent of the external sector. Projection commutes with the negative modes, and injection transports every target current mode. Mapping the two native finite normal-product sums proves the equality. The finite coefficient arguments of LatticeCosetOperatorCorrection consume this recursion in the all-source inner creation expansion.", DescribeRole.Theorem),
            Paragraph(Text("The source recurrence is the native lattice field recurrence of Bakalov-Kac, math/0402315v1, section 4.1. No occurrence-list independence, PBW reconstruction or new vertex algebra is assumed.")))));
}
