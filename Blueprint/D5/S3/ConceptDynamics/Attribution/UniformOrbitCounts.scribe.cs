using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class UniformOrbitCountsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ConceptDynamics/Attribution/UniformOrbitCounts";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer counts of events under equivariant maps to a finite set.",
        H("Equivariant seed counts on table orbits"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("realize-orbit-copy-counts"),
                DeclarationHandle.Create(Owner + ".realize_orbit_copy_counts"),
                H("Orbit multiplicities give equivariant copies"),
                StatementSource.FromAuthor(Count()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let a group act on a finite set T. For each orbit O, prescribe "
                        + "a nonnegative integer n(O) giving the number of copies of every element "
                        + "in O. There is a finite seed set with a group action and an equivariant "
                        + "map to T. A seed is fixed by a subgroup exactly when its image is. "
                        + "For any event A in T, its number of seed preimages is the displayed sum.")),
                    Paragraph(Text("The action transports the underlying element and preserves the "
                        + "copy index. This construction includes zero multiplicities and empty sets."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("count-seed-fibers-by-orbit"),
                DeclarationHandle.Create(Owner + ".count_seed_fibers_by_orbit"),
                H("Every equivariant seed map has orbit multiplicities"),
                StatementSource.FromAuthor(Count()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let a group act on finite sets S and T, and let f from S to T "
                        + "be equivariant. There is one nonnegative integer n(O) per orbit of T "
                        + "such that the seed count of each event A is the displayed sum.")),
                    Paragraph(Text("A group element transports the seed fiber over t bijectively "
                        + "to the fiber over its translate. Hence the fiber size is constant on "
                        + "each orbit. Equivariance is used in this step. For a two-element orbit, "
                        + "a map from a singleton to just one element has unequal fiber sizes."))),
                DescribeRole.Theorem))));

    private static Formula Count()
    {
        Formula a = F.Id("A");
        Formula o = F.Id("O");
        return Disp(Seq(F.Id("C"), Open, a, Close, Sp, Eq, Sp, new Formula.Subscript(Sum, o), Sp,
            F.Id("c"), Open, a, Comma, o, Close, Sp, F.Id("n"), Open, o, Close));
    }
}
