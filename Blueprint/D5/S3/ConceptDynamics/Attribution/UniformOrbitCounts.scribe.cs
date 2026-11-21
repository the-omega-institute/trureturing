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
                    Paragraph(Text("Let a group act on a finite source S and a target T with finitely many orbits, and let f from S to T "
                        + "be equivariant. There is one nonnegative integer n(O) per orbit of T "
                        + "such that the seed count of each finite event A is the displayed sum.")),
                    Paragraph(Text("A group element transports the seed fiber over t bijectively "
                        + "to the fiber over its translate. Hence the fiber size is constant on "
                        + "each orbit. Equivariance is used in this step. For a two-element orbit, "
                        + "a map from a singleton to just one element has unequal fiber sizes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("orbit-event-counts-match-fiber"),
                DeclarationHandle.Create(Owner + ".orbit_event_counts_match_fiber"),
                H("The integer fiber characterizes exact equivariant event counts"),
                StatementSource.FromAuthor(Fiber()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let a group act on a finite table set T. Choose a finite indexed "
                        + "family of events E(i) in T and an integer target vector w. The additive "
                        + "map M has entry M(i, O) equal to the size of the intersection of E(i) "
                        + "with orbit O. Fix a natural degree k.")),
                    Paragraph(Text("The fiber at k w contains a nonnegative integer vector exactly "
                        + "when there exist a finite seed set S with a group action and an "
                        + "equivariant map f from S to T that realizes the displayed event counts. "
                        + "For every subgroup H and seed s, H fixes s exactly when H fixes f(s).")),
                    Paragraph(Text("A vector in the fiber gives the number of copies of each table "
                        + "in its orbit, with the group action preserving the copy index. In the "
                        + "other direction equivariance transports seed fibers along the orbit, "
                        + "so the fiber cardinalities give a single nonnegative vector that "
                        + "satisfies every event equation together. Degree zero allows an empty seed "
                        + "set."))),
                DescribeRole.Theorem))));

    private static Formula Count()
    {
        Formula a = F.Id("A");
        Formula o = F.Id("O");
        return Disp(Seq(F.Id("C"), Open, a, Close, Sp, Eq, Sp, new Formula.Subscript(Sum, o), Sp,
            F.Id("c"), Open, a, Comma, o, Close, Sp, F.Id("n"), Open, o, Close));
    }

    private static Formula Fiber()
    {
        Formula i = F.Id("i");
        Formula k = F.Id("k");
        Formula w = F.Id("w");
        Formula n = F.Id("n");
        Formula seeds = F.Id("S");
        Formula f = F.Id("f");
        return Disp(Seq(
            Open, Exists, Sp, n, Sp, Geq, Sp, D(0), Comma, Sp,
            Call("M", n), Sp, Eq, Sp, k, w, Close,
            Sp, Iff, Sp, Open, Exists, Sp, seeds, Comma, Sp, f, Comma, Sp,
            Call("Equivariant", f), Sp, Land, Sp, Call("ReflectsFixedness", f), Sp, Land, Sp,
            Open, Forall, Sp, i, Comma, Sp,
            Call("C", seeds, f, Call("E", i)), Sp, Eq, Sp, k, new Formula.Subscript(w, i), Close, Close));
    }
}
