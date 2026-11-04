using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Rauzy;

internal sealed class TribonacciRegularClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "The original Tribonacci Rauzy fractal is the closure of its interior under the two characteristic-root hypotheses.",
            H("Regular closure of the Tribonacci Rauzy fractal"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("tribonacci-rauzy-prefix-cover"),
                    DeclarationHandle.Create("D5/S3/Geometry/Rauzy/TribonacciRegularClosure.rauzyFractal_prefix_cover"),
                    H("Exact three-map cover"), StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                        "The existing name split equivalence reconstructs the three initial "
                        + "blocks through the coordinate identity for adjoining a Boolean digit. Lengths zero, one "
                        + "and two are handled directly by 0, 1, z and 1+z. The finite window "
                        + "is covered in reverse, and compact closed affine images extend "
                        + "the cover to the Rauzy closure. Thus every point in the fractal is "
                        + "the image of another point under one of the three prefix maps. "
                        + "Together with nonempty interior, this equality implies regular closure."))), DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-rauzy-regular-closure"),
                    DeclarationHandle.Create("D5/S3/Geometry/Rauzy/TribonacciRegularClosure.rauzyFractal_closure_interior"),
                    H("The actual Rauzy closure is regular closed"), StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Let z be a root of X^3 - X^2 - X - 1 distinct from the real Tribonacci constant beta. "
                        + "The set K is the closure "
                        + "of finite exponent-zero admissible Boolean sums. "
                        + "The split of admissible names into prefixes 0, 10 and 110 gives the reverse cover; "
                        + "the coordinate identity for adjoining a digit evaluates each prefix, and short names give "
                        + "0, 1, z and 1+z. Compact images extend this to exact equality for the three prefix maps. "
                        + "The nonempty-interior theorem supplies an open patch. The "
                        + "secondary-root relation beta norm(z)^2 = 1 proves z is nonzero; the root norm bound "
                        + "gives one common contraction constant norm(z) for z, z^2 and z^3. Their affine maps "
                        + "are open by multiplication homeomorphisms and translations. The parametric compact "
                        + "metric theorem gives closure(interior K) = K. Exact self-coverage and nonempty "
                        + "interior both follow from the two stated conditions on z. "
                        + "The three maps are w ↦ z w, w ↦ 1 + z^2 w, and w ↦ 1 + z + z^3 w."))), DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Topology/ContractingCoverRegularClosure")),
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Geometry/Rauzy/TribonacciInterior")),
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Tower/Tribonacci/RauzyFractal"))
            ]));
    }
}
