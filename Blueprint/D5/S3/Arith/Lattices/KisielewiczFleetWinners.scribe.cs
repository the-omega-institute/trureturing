using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class KisielewiczFleetWinnersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two fixed nonperiodic cube fleets have a non-eventually-periodic winner sequence.",
        H("Nonperiodic cube fleets with infinitely many winner changes"),
        Blocks(
            Paragraph(Text("A fleet consists of lattice origins whose translates of the discrete "
                + "unit cube {0,1}³ cover each lattice point exactly once. The fleet has a trivial "
                + "translation stabilizer if only the zero translation preserves the origin set. "
                + "The base point is zero and the coordinate labels are fixed.")),
            Paragraph(Text("For any positive integral side a and shift e in {0,1}³, a score counts "
                + "the fleet origins t with eᵢ ≤ tᵢ < eᵢ + a in each coordinate. The margin is "
                + "the sum of signed score differences over the 64 equally likely ordered shift "
                + "pairs. The outcome O is the sign of that margin.")),
            Describe.Lean(DescribeId.Create("exists-nonperiodic-fleets"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Lattices/KisielewiczFleetWinners.exists_nonperiodic_fleets"),
                H("Two fixed fleets with no eventual outcome period"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Geometry/kisielewicz2026cubetilings")),
                Blocks(
                    Paragraph(Text("Divide the vertical coordinate by two to choose a slab. In each "
                        + "ordinary slab the horizontal grid has one common parity. The exceptional "
                        + "row in slab −1 and exceptional column in slab −2 preserve unique cover "
                        + "and eliminate all nonzero translation periods.")),
                    Paragraph(Text("At tₖ = 8ᵏ⁺¹(k+1)!, prescribe phase-zero totals 2tₖ and 3tₖ "
                        + "through slab 4tₖ+1 and swap them at alternate k. Each increment fits in "
                        + "its new block. The literal margin at side 8tₖ+3 is +4 or −4 according "
                        + "to that assignment. For every positive P, sufficiently late consecutive "
                        + "selected sides are both 3 modulo P. Their opposite outcomes force a "
                        + "change in some step of length P between them."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kisielewicz-2026-nonperiodic-fleet-winners"),
                    ResolutionKind.Proved)))));

    private static Formula Statement()
    {
        var f = F.Id("F");
        var g = F.Id("G");
        var a = F.Id("a");
        var b = F.Id("b");
        var c = F.Id("c");
        var p = F.Id("P");
        var cutoff = F.Id("B");
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        var lattice = Seq(Mathbb, Grp(F.Id("Z")), Caret, Grp(D(3)));
        var bound = Seq(Max, Par(Seq(D(1), Comma, cutoff)));
        return Disp(Seq(
            Exists, Sp, f, Comma, g, Sp, Subseteq, Sp, lattice, Comma, Sp,
            Predicate("UniqueCover", f), Sp, Land, Sp, Predicate("UniqueCover", g), Sp, Land, Sp,
            Predicate("TrivialStabilizer", f), Sp, Land, Sp,
            Predicate("TrivialStabilizer", g), Sp, Land, Sp,
            Par(Seq(Forall, Sp, cutoff, Sp, InMacro, Sp, naturals, Comma, Sp,
                Exists, Sp, a, Comma, b, Sp, InMacro, Sp, naturals, Comma, Sp,
                bound, Sp, Le, Sp, a, Sp, Land, Sp, bound, Sp, Le, Sp, b, Sp, Land, Sp,
                Outcome(a), Sp, Eq, Sp, D(1), Sp, Land, Sp,
                Outcome(b), Sp, Eq, Sp, Minus, D(1))), Sp, Land, Sp,
            Par(Seq(Forall, Sp, p, Sp, InMacro, Sp, naturals, Comma, Sp, D(0), Sp, Lt, Sp,
                p, Sp, Rightarrow, Sp, Forall, Sp, cutoff, Sp, InMacro, Sp, naturals, Comma, Sp,
                Exists, Sp, c, Sp, InMacro, Sp, naturals, Comma, Sp, bound, Sp, Le, Sp, c,
                Sp, Land, Sp, Outcome(Seq(c, Sp, Plus, Sp, p)), Sp, Neq, Sp, Outcome(c)))));
    }

    private static Formula Par(Formula value) => Seq(Open, value, Close);

    private static Formula Predicate(string name, Formula argument) =>
        Seq(Operatorname, Grp(F.Id(name)), Par(argument));

    private static Formula Outcome(Formula side) =>
        Seq(F.Id("O"), Underscore, Grp(F.Id("F"), Comma, F.Id("G")), Par(side));
}
