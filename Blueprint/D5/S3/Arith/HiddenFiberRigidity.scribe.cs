using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class HiddenFiberRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Arith/HiddenFiberRigidity",
            "A continuous map from a connected real interval into the profinite fiber product is constant."),
        H("Rigidity of the Hidden Profinite Fiber"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("a-continuous-interval-map-into-the-profinite-fiber-is-constant"),
                H("A continuous interval map into the profinite fiber is constant"),
                LeanTheorem(
                    "D5/S3/Arith/HiddenFiberRigidity.hidden_fiber_rigidity"),
                LatexStatement.Create(
                    @"$$s \subseteq \mathbb{R} \text{ preconnected} \land f : s \to \prod_{p \text{ prime}} "
                    + @"\mathbb{Z}_p \text{ continuous} \Rightarrow \forall x, y \in s,\ f(x) = f(y)$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The hidden fiber K_infinity is the product of the rings of p-adic integers over "
                        + "all primes, carrying the product topology under which a map is continuous exactly "
                        + "when each coordinate reading into a single p-adic factor is continuous. The theorem "
                        + "fixes an arbitrary preconnected subset s of the real line as the domain and a map f "
                        + "continuous on s into this fiber product, and concludes that f is constant on s: any "
                        + "two arguments in s share the same image. The preconnected hypothesis is not a "
                        + "weakening of the informal connected interval but its exact characterization, since "
                        + "the preconnected subsets of the real line are precisely its intervals; the "
                        + "conclusion therefore covers every connected real interval without loss.")),
                    Paragraph(Text(
                        "The proof is the profinite reading of the informal layerwise argument. Each factor is "
                        + "an ultrametric metric space, hence totally separated and a fortiori totally "
                        + "disconnected; the arbitrary product of totally disconnected spaces is again totally "
                        + "disconnected, so the fiber product is totally disconnected. The continuous image of "
                        + "the preconnected domain is preconnected, and a preconnected subset of a totally "
                        + "disconnected space is a subsingleton. The two candidate images thus coincide. The "
                        + "layerwise projection to a discrete residue quotient of the informal proof is "
                        + "subsumed here by total disconnectedness of the factors, which is the topological "
                        + "content of the reading being single-valued on any connected source. The result is "
                        + "purely topological: it asserts no arithmetic of the p-adic factors and no numerical "
                        + "certificate.")))
            ))));
}
