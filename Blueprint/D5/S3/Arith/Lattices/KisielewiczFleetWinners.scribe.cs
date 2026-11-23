using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class KisielewiczFleetWinnersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/KisielewiczFleetWinners.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/kisielewicz2026cubetilings");
    private static readonly Formula Integers = Seq(Mathbb, Grp(F.Id("Z")));
    private static readonly Formula Naturals = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula Origin = Operator("Origin");
    private static readonly Formula Shift = Operator("Shift");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two fixed nonperiodic cube fleets have a non-eventually-periodic winner sequence.",
        H("Nonperiodic cube fleets with infinitely many winner changes"),
        Blocks(
            Paragraph(Text("The base point is zero and the coordinate labels are fixed.")),
            Definition("origin", "Origin", "Lattice origins",
                Seq(Origin, Sp, Eq, Sp, Integers, Sp, Times, Sp, Integers, Sp, Times, Sp, Integers),
                "An origin specifies the three integer coordinates of a cube."),
            Definition("shift", "Shift", "Window shifts",
                Seq(Shift, Sp, Eq, Sp, Operator("Bool"), Sp, Times, Sp, Operator("Bool"),
                    Sp, Times, Sp, Operator("Bool")),
                "Each coordinate shifts the base point by zero or one."),
            Definition("bit", "bit", "Shift coordinate", Bit(),
                "The Boolean coordinates are interpreted as integers."),
            Definition("axis", "axis", "One coordinate of the window", Axis(),
                "The integer interval contains its lower endpoint and excludes its upper endpoint."),
            Definition("box", "box", "Window of origins", Box(),
                "The three intervals use the same natural side and the corresponding shift coordinates."),
            Definition("score", "score", "Number of fleet origins in the window", Score(),
                "The score is the cardinality of the fleet origins in the shifted window."),
            Definition("margin", "margin", "Signed comparison of two fleets", Margin(),
                "All 64 ordered shift pairs are equally likely. Each pair contributes one, zero, "
                + "or minus one according to the comparison of the two integer-valued counts."),
            Definition("outcome", "outcome", "Strict winner", OutcomeDefinition(),
                "The sign gives one for a strict win by the first fleet, minus one for a strict "
                + "win by the second fleet, and zero when the win probabilities are equal."),
            Definition("covers", "Covers", "Membership in a translated discrete cube", Covers(),
                "Each coordinate of the point differs from the origin by zero or one."),
            Definition("unique-cover", "UniqueCover", "Unique lattice cover", UniqueCover(),
                "Every lattice point belongs to the cube of exactly one fleet origin."),
            Definition("trivial-stabilizer", "TrivialStabilizer", "Trivial translation stabilizer",
                TrivialStabilizer(), "A translation preserves the fleet when it preserves origin membership."),
            Describe.Lean(DescribeId.Create("exists-nonperiodic-fleets"),
                DeclarationHandle.Create(Prefix + "exists_nonperiodic_fleets"),
                H("Two fixed fleets with no eventual outcome period"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(Source),
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
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Definition(string id, string name, string title,
        Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Bit() =>
        Seq(Call("bit", Operator("false")), Sp, Eq, Sp, D(0), Comma, Quad,
            Call("bit", Operator("true")), Sp, Eq, Sp, D(1));

    private static Formula Axis()
    {
        var a = F.Id("a");
        var s = F.Id("s");
        var x = F.Id("x");
        var start = Call("bit", s);
        return Seq(Call("axis", a, s), Sp, Eq, Sp, OpenBrace, x, Sp, InMacro, Sp, Integers, Sp,
            Mid, Sp, start, Sp, Le, Sp, x, Sp, Lt, Sp, start, Sp, Plus, Sp, AsInteger(a), CloseBrace);
    }

    private static Formula Box()
    {
        var a = F.Id("a");
        var x = Coordinate("s", D(1));
        var y = Coordinate("s", D(2));
        var z = Coordinate("s", D(3));
        return Seq(Call("box", a, Par(Seq(x, Comma, Sp, y, Comma, Sp, z))), Sp, Eq, Sp,
            Call("axis", a, x), Sp, Times, Sp, Call("axis", a, y), Sp, Times, Sp, Call("axis", a, z));
    }

    private static Formula Score()
    {
        var f = F.Id("F");
        var a = F.Id("a");
        var s = F.Id("s");
        var t = F.Id("t");
        return Seq(Call("score", f, a, s), Sp, Eq, Sp,
            Call("card", Seq(OpenBrace, t, Sp, InMacro, Sp, Call("box", a, s), Sp,
                Mid, Sp, t, Sp, InMacro, Sp, f, CloseBrace)));
    }

    private static Formula Margin()
    {
        var f = F.Id("F");
        var g = F.Id("G");
        var a = F.Id("a");
        var e = F.Id("e");
        var s = F.Id("s");
        var pairs = Seq(Par(Seq(e, Comma, Sp, s)), Sp, InMacro, Sp, Shift, Sp, Times, Sp, Shift);
        var difference = Seq(AsInteger(Call("score", f, a, e)), Sp, Minus, Sp,
            AsInteger(Call("score", g, a, s)));
        return Seq(Call("margin", f, g, a), Sp, Eq, Sp,
            new Formula.Subscript(Sum, pairs), Sp, Call("sign", difference));
    }

    private static Formula OutcomeDefinition()
    {
        var f = F.Id("F");
        var g = F.Id("G");
        var a = F.Id("a");
        return Seq(Call("outcome", f, g, a), Sp, Eq, Sp, Call("sign", Call("margin", f, g, a)));
    }

    private static Formula Covers()
    {
        var t = F.Id("t");
        var p = F.Id("p");
        var i = F.Id("i");
        var originCoordinate = Coordinate("t", i);
        var pointCoordinate = Coordinate("p", i);
        return Seq(Call("Covers", t, p), Sp, Iff, Sp, Par(Seq(Forall, Sp, i, Sp, InMacro, Sp,
            OpenBrace, D(1), Comma, D(2), Comma, D(3), CloseBrace, Comma, Sp,
            originCoordinate, Sp, Le, Sp, pointCoordinate, Sp, Lt, Sp, originCoordinate, Sp, Plus, Sp, D(2))));
    }

    private static Formula UniqueCover()
    {
        var f = F.Id("F");
        var t = F.Id("t");
        var p = F.Id("p");
        return Seq(Call("UniqueCover", f), Sp, Iff, Sp,
            Par(Seq(Forall, Sp, p, Sp, InMacro, Sp, Origin, Comma, Sp,
                Exists, Bang, Sp, t, Sp, InMacro, Sp, f, Comma, Sp, Call("Covers", t, p))));
    }

    private static Formula TrivialStabilizer()
    {
        var f = F.Id("F");
        var t = F.Id("t");
        var d = F.Id("d");
        var preserves = Par(Seq(Forall, Sp, t, Sp, InMacro, Sp, Origin, Comma, Sp,
            t, Sp, Plus, Sp, d, Sp, InMacro, Sp, f, Sp, Iff, Sp, t, Sp, InMacro, Sp, f));
        return Seq(Call("TrivialStabilizer", f), Sp, Iff, Sp,
            Par(Seq(Forall, Sp, d, Sp, InMacro, Sp, Origin, Comma, Sp,
                preserves, Sp, Rightarrow, Sp, d, Sp, Eq, Sp, Par(Seq(D(0), Comma, D(0), Comma, D(0))))));
    }

    private static Formula Statement()
    {
        var f = F.Id("F");
        var g = F.Id("G");
        var a = F.Id("a");
        var b = F.Id("b");
        var c = F.Id("c");
        var p = F.Id("P");
        var cutoff = F.Id("B");
        var lattice = Seq(Mathbb, Grp(F.Id("Z")), Caret, Grp(D(3)));
        var bound = Seq(Max, Par(Seq(D(1), Comma, cutoff)));
        return Disp(Seq(
            Exists, Sp, f, Comma, g, Sp, Subseteq, Sp, lattice, Comma, Sp,
            Call("UniqueCover", f), Sp, Land, Sp, Call("UniqueCover", g), Sp, Land, Sp,
            Call("TrivialStabilizer", f), Sp, Land, Sp,
            Call("TrivialStabilizer", g), Sp, Land, Sp,
            Par(Seq(Forall, Sp, cutoff, Sp, InMacro, Sp, Naturals, Comma, Sp,
                Exists, Sp, a, Comma, b, Sp, InMacro, Sp, Naturals, Comma, Sp,
                bound, Sp, Le, Sp, a, Sp, Land, Sp, bound, Sp, Le, Sp, b, Sp, Land, Sp,
                Call("outcome", f, g, a), Sp, Eq, Sp, D(1), Sp, Land, Sp,
                Call("outcome", f, g, b), Sp, Eq, Sp, Minus, D(1))), Sp, Land, Sp,
            Par(Seq(Forall, Sp, p, Sp, InMacro, Sp, Naturals, Comma, Sp, D(0), Sp, Lt, Sp,
                p, Sp, Rightarrow, Sp, Forall, Sp, cutoff, Sp, InMacro, Sp, Naturals, Comma, Sp,
                Exists, Sp, c, Sp, InMacro, Sp, Naturals, Comma, Sp, bound, Sp, Le, Sp, c,
                Sp, Land, Sp, Call("outcome", f, g, Seq(c, Sp, Plus, Sp, p)), Sp, Neq, Sp,
                Call("outcome", f, g, c)))));
    }

    private static Formula Par(Formula value) => Seq(Open, value, Close);

    private static Formula Operator(string name) => Seq(Operatorname, Grp(F.Id(name)));

    private static Formula Call(string name, Formula argument) => Seq(Operator(name), Par(argument));

    private static Formula Call(string name, Formula first, Formula second) =>
        Call(name, Seq(first, Comma, Sp, second));

    private static Formula Call(string name, Formula first, Formula second, Formula third) =>
        Call(name, Seq(first, Comma, Sp, second, Comma, Sp, third));

    private static Formula Coordinate(string name, Formula index) =>
        new Formula.Subscript(F.Id(name), index);

    private static Formula AsInteger(Formula value) => Par(Seq(value, Sp, Colon, Sp, Integers));
}
