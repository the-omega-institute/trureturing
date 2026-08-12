using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class HiddenFiberRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A continuous map from a connected real interval into the profinite fiber product is constant.",
        H("Rigidity of the Hidden Profinite Fiber"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-continuous-interval-map-into-the-profinite-fiber-is-constant"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/HiddenFiberRigidity.hidden_fiber_rigidity"),
                H("A continuous interval map into the profinite fiber is constant"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("s"), Sp, Subseteq, Sp, Mathbb, Grp(F.Id("R")), Sp, F.Text, Grp(Sp, F.Id("preconnected")), Sp, Land, Sp, F.Id("f"), Sp, Colon, Sp, F.Id("s"), Sp, To, Sp, Prod, Underscore, Grp(F.Id("p"), Sp, F.Text, Grp(Sp, F.Id("prime"))), Sp, Mathbb, Grp(F.Id("Z")), Underscore, F.Id("p"), Sp, F.Text, Grp(Sp, F.Id("continuous")), Sp, Rightarrow, Sp, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Sp, InMacro, Sp, F.Id("s"), Comma, Esc, F.Id("f"), Open, F.Id("x"), Close, Sp, Eq, Sp, F.Id("f"), Open, F.Id("y"), Close))),
                AssessedProvenance.FromRepo(),
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
                        + "certificate."))),
                DescribeRole.Theorem))));
}
