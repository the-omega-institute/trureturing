using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class MamedeNonoscSourceEndpointsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonoscillating word determines strict interior source endpoints in either extremal orientation.",
        H("Nonoscillating Source Endpoints"),
        Blocks(Describe.Lean(
            DescribeId.Create("mamede-nonosc-first-orientation-endpoints"),
            DeclarationHandle.Create(
                "D5/S1/Words/Permutations/MamedeNonoscSourceEndpoints.first_orientation_strict_endpoints"),
            H("Strict endpoints from an actual source word"),
            StatementSource.FromAuthor(Disp(Q(
                Call("SingletonWord", V("n"), V("sigma"), V("a")), Land,
                Call("AttainedGeneratorExtrema", V("m"), V("M"), V("a")), Land,
                Call("GeneratorInterval", V("n"), V("m"), V("M"), V("a")), Land,
                Call("FirstOrientationMap", V("n"), V("m"), V("M"), V("sigma")), Land,
                Neg, Call("Oscillation", V("a")),
                Implies, V("m"), Lt, V("M"), Land, Exists, V("i"), V("j"), Comma,
                Call("StrictInterior", V("m"), V("i"), V("j"), V("M")), Land,
                Call("RemainingSourceMaps", V("n"), V("m"), V("M"), V("i"),
                    V("j"), V("sigma")), Land,
                Call("ExteriorFixed", V("n"), V("m"), V("M"), V("sigma"))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let a be a singleton reduced consecutive word for sigma, with attained "
                + "minimum m and maximum M, 1<=m<=M<=n, and all letters in [m,M]. "
                + "Assume sigma sends one-based position M+1 to m and a is not an "
                + "oscillation. Then m<M. Set i to the one-based inverse image of M+1 "
                + "under sigma, and j+1 to the image of m. The theorem proves "
                + "m<i<M and m<j<M, together with sigma(i)=M+1, sigma(m)=j+1, "
                + "and fixed positions outside [m,M+1]. It assumes no source shape or "
                + "remaining endpoint equation. Exterior fixedness and injectivity give "
                + "the weak image bounds. The opposite-extremal-maps theorem excludes "
                + "i=m and j=M, which would force oscillation. At i=M or j=m, a guarded "
                + "strand walk forces an attained extremum at the last or first word "
                + "letter, again forcing oscillation. The m=M case is also excluded by "
                + "the endpoint-oscillation theorem. The result leaves i and j unordered. "
                + "For i<=j its data satisfy the shape extractor's endpoint predicate; "
                + "for j<i they satisfy the order-free fiber theorem's endpoint inputs. "
                + "Neither case is a global singleton-class count."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("mamede-nonosc-reflected-orientation-endpoints"),
            DeclarationHandle.Create(
                "D5/S1/Words/Permutations/MamedeNonoscSourceEndpoints.reflected_orientation_strict_endpoints"),
            H("Strict endpoints in the reflected orientation"),
            StatementSource.FromAuthor(Disp(Q(
                Call("SingletonWord", V("n"), V("sigma"), V("a")), Land,
                Call("AttainedGeneratorExtrema", V("m"), V("M"), V("a")), Land,
                Call("GeneratorInterval", V("n"), V("m"), V("M"), V("a")), Land,
                Call("ReflectedOrientationMap", V("n"), V("m"), V("M"), V("sigma")), Land,
                Neg, Call("Oscillation", V("a")),
                Implies, V("m"), Lt, V("M"), Land, Exists, V("i"), V("j"), Comma,
                Call("StrictInterior", V("m"), V("i"), V("j"), V("M")), Land,
                Call("ReflectedSourceMaps", V("n"), V("m"), V("M"), V("i"),
                    V("j"), V("sigma")), Land,
                Call("ExteriorFixed", V("n"), V("m"), V("M"), V("sigma"))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let a be a singleton reduced consecutive word for sigma, with attained "
                + "minimum m and maximum M, 1<=m<=M<=n, and all letters in [m,M]. "
                + "Assume sigma(m)=M+1 in one-based positions and a is nonoscillating. "
                + "Then m<M and there are i,j with m<i<M and m<j<M, "
                + "sigma(j+1)=m, sigma(M+1)=i, and fixed positions outside [m,M+1]. "
                + "The witnesses correspond to i=sigma(M+1) and j+1=inverse(sigma)(m). "
                + "The exact reversal-invariance theorem makes reverse(a) a "
                + "nonoscillating singleton word for inverse(sigma). Applying the "
                + "first-orientation theorem there and transporting its equations "
                + "back proves the displayed maps. No source shape or further position "
                + "equation is assumed; m=M and boundary witnesses are excluded by "
                + "the same proof. For i<=j, the data feed the source shape and deletion "
                + "theorems for inverse(sigma); for j<i, they feed whole-fiber uniqueness "
                + "there, which word reversal transfers to sigma. A reflected deletion "
                + "equivalence in the original convention and the global induction "
                + "are separate obligations."))),
            DescribeRole.Theorem))));

    private static Formula Q(params Formula[] items)
    {
        var spaced = new Formula[items.Length * 2 - 1];
        for (var i = 0; i < items.Length; i++)
        {
            spaced[2 * i] = items[i];
            if (i + 1 < items.Length) spaced[2 * i + 1] = Sp;
        }
        return Seq(spaced);
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Q(Operatorname, Grp(V(name))), [.. args]);
}
