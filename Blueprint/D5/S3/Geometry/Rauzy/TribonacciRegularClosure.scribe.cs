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
                    DescribeId.Create("tribonacci-rauzy-regular-closure"),
                    DeclarationHandle.Create("D5/S3/Geometry/Rauzy/TribonacciRegularClosure.rauzyFractal_closure_interior"),
                    H("The actual Rauzy closure is regular closed"), StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The only hypotheses are membership of z in the existing characteristic-root multiset "
                        + "and inequality to the real Tribonacci constant beta. The set K is the existing closure "
                        + "of finite exponent-zero admissible Boolean sums. "
                        + "The genuine reverse cover is proved in the symbolic owner RauzyFractal using "
                        + "tribonacciNameSplitEquiv and its existing coordinate supplier; the short names give "
                        + "0, 1, z and 1+z. Compact images extend this to exact equality for the three prefix maps. "
                        + "The existing nonempty-interior theorem supplies the open patch. The existing "
                        + "secondary-root relation beta norm(z)^2 = 1 proves z is nonzero; the root norm bound "
                        + "gives one common contraction constant norm(z) for z, z^2 and z^3. Their affine maps "
                        + "are open by multiplication homeomorphisms and translations. The parametric compact "
                        + "metric theorem now gives closure(interior K) = K. Neither exact cover, nonempty "
                        + "interior, nor a closed invariant core is smuggled in as an extra root hypothesis. "
                        + "The affine helpers and symbolic cover are consumed prerequisites, not separate advances. "
                        + "This application concerns the same Rauzy geometry described in TribonacciInterior; "
                        + "it makes no new originality, boundary-volume, tiling or connectedness claim."))), DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Topology/ContractingCoverRegularClosure")),
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Geometry/Rauzy/TribonacciInterior")),
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Tower/Tribonacci/RauzyFractal"))
            ]));
    }
}
