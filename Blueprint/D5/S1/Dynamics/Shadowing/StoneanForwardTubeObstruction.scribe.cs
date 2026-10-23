using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class StoneanForwardTubeObstructionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/StoneanForwardTubeObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An infinite disjoint open forward tube in an extremally disconnected source rules out finite-cover shadowing.",
        H("A Projective Cover Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("stonean-forward-tube-obstruction"),
                DeclarationHandle.Create(Owner + "not_has_shadowing_of_disjoint_open_forward_tubes"),
                H("Disjoint open forward tubes exclude shadowing"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Dynamics/gleason1958projective")),
                Blocks(
                    Paragraph(Text(
                        "Let Y be any extremally disconnected topological space, g a continuous self-map, "
                        + "and U(n) open sets indexed by all natural numbers. Assume distinct U(n) are disjoint, "
                        + "U(0) is nonempty, and g maps U(n) into U(n+1). Then g does not have finite-open-cover "
                        + "shadowing. Compactness, Hausdorff separation, metrizability, countable weight, onto "
                        + "dynamics and density of the tube union are not hypotheses.")),
                    Paragraph(Text(
                        "The closure W of the union of U(2^k) is clopen. Its continuous binary indicator "
                        + "on U(n) is true exactly at powers of two. Every finite itinerary starting with true "
                        + "has a nonempty open cylinder meeting W, hence the closure of the whole tube union. "
                        + "It therefore occurs on some tube. Consecutive true observations are separated by "
                        + "a power-of-two distance, and all these distances occur.")),
                    Paragraph(Text(
                        "The existing finite_observation_isSofic theorem would give one finite graph for "
                        + "the entire observed language. With N vertices, an actual tube orbit gives distance "
                        + "D=2^(N+2) between consecutive true labels. Vertices at times 1 through N+1 repeat "
                        + "at times i<j. Erasing that zero cycle preserves the complete infinite suffix and "
                        + "creates distance D-(j-i), strictly between 2^(N+1) and 2^(N+2). This contradicts "
                        + "the tube-cylinder restriction. Finite-cylinder soundness follows from openness and density "
                        + "in the closure of the tube union.")),
                    Paragraph(Text(
                        "For Peng Question 5.1, take the compact convergent sequence N with its point at infinity "
                        + "and successor fixing infinity. Initial-singleton and tail partitions prove shadowing; "
                        + "the source is already zero-dimensional and its identity cover works. Fibers over the "
                        + "isolated natural points of any onto equivariant extremally disconnected cover are "
                        + "precisely such open forward tubes. Thus every such cover, and by Gleason every "
                        + "projective compact Hausdorff cover, fails shadowing for every continuous lift. "
                        + "This application is explained in the problem dossier; it is not a negative answer "
                        + "to Question 5.1 or a worldwide originality claim.")),
                    Paragraph(Text(
                        "The finite-observation theorem supplies an exact complete graph language. Clopen "
                        + "Boolean indicators, finite pigeonhole and powers supply the other ingredients. "
                        + "The obstruction couples "
                        + "arbitrary clopen coloring of open tubes to an exact finite-cylinder restriction and "
                        + "a whole-path cycle erasure. The still missing all-face construction must control its "
                        + "clopen observations without demanding projectivity, and must prove every live finite "
                        + "word source-feasible with coherent whole deletion lifts or Mittag-Leffler images."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula y = F.Id("Y"), g = F.Id("g"), u = F.Id("U");
        Formula n = F.Id("n"), i = F.Id("i"), j = F.Id("j");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula un = Apply(u, n), ui = Apply(u, i), uj = Apply(u, j);
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, y, Colon, Sp, F.Id("Type"), Comma, Sp,
                OpenBracket, Call("TopologicalSpace", y), CloseBracket, Sp,
                OpenBracket, Call("ExtremallyDisconnected", y), CloseBracket, Comma),
            Seq(Forall, Sp, g, Colon, Sp, y, Sp, Rightarrow, Sp, y, Comma, Sp,
                u, Colon, Sp, nat, Sp, Rightarrow, Sp, Call("Set", y), Comma),
            Seq(Call("Continuous", g), Sp, Rightarrow, Sp,
                Open, Forall, Sp, n, Colon, Sp, nat, Comma, Sp, Call("IsOpen", un), Close,
                Sp, Rightarrow),
            Seq(Open, Forall, Sp, i, Comma, Sp, j, Colon, Sp, nat, Comma, Sp,
                i, Sp, Neq, Sp, j, Sp, Rightarrow, Sp, Call("Disjoint", ui, uj), Close,
                Sp, Rightarrow),
            Seq(Call("Nonempty", Apply(u, D(0))), Sp, Rightarrow, Sp,
                Open, Forall, Sp, n, Colon, Sp, nat, Comma, Sp,
                Call("MapsTo", g, un, Apply(u, Seq(n, Plus, D(1)))), Close, Sp, Rightarrow, Sp,
                new Formula.Not(Call("HasShadowing", g)), Dot)
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
