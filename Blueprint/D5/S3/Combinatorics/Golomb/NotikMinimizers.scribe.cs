
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Golomb;

internal sealed class NotikMinimizersDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Combinatorics/Golomb/NotikMinimizers";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/notik2026golomb");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All normalized real Golomb minimizers at eight, nine, and ten marks are integral.",
        H("Notik's real Golomb minimizers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("notik-golomb-minimum-at"),
                DeclarationHandle.Create(Gid + ".MinimumAt"),
                H("Attainment, lower bound, and integrality at equality"),
                StatementSource.FromAuthor(MinimumDefinition()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For n gaps there are n + 1 marks, indexed from zero to n. "
                    + "G denotes the real ruler predicate, L(x) is the last mark minus the first, "
                    + "and iota is the coordinatewise integer-to-real cast on a tuple or the "
                    + "integer-to-real cast on a single value. The lower bound applies to every "
                    + "real ruler, and integrality is asserted with the first mark fixed at zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("notik-golomb-minimizers"),
                DeclarationHandle.Create(Gid + ".result"),
                H("The minimum-length real and integer rulers coincide at all three sizes"),
                StatementSource.FromAuthor(Disp(Conjoin(
                    Minimum(D(7), D(3, 4)), Minimum(D(8), D(4, 4)), Minimum(D(9), D(5, 5))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Esther Notik's Section 10 asks whether the shortest real rulers at eight, nine, "
                        + "and ten marks are precisely the optimal integer rulers. The three lengths "
                        + "are 34, 44, and 55. Strictly ordered integer tuples with distinct distances "
                        + "satisfy real unit separation. This gives the reverse inclusion after the "
                        + "lower bounds and integral attainment have fixed the same minimum lengths.")),
                    Paragraph(Text(
                        "Notik's bound trees have 3,823, 15,929, and 18,425 nodes in size order. "
                        + "The replay uses the archived bounds for five through seven marks and "
                        + "extends the collection of smaller bounds after proving each new length. "
                        + "Each root check joins the subtree equations in branch order, using the "
                        + "inherited rows and the certificates for all 349, 1,235, and 1,209 tied leaves.")),
                    Paragraph(Text(
                        "A feasible optimum follows a branch in one of its two orientations. "
                        + "Every positively weighted row at a tied leaf is tight. The certificates "
                        + "use these rows and the separation constraints to force each gap to be an "
                        + "integer, or to exclude the remaining cases. Reversing the gap order "
                        + "preserves integrality, and summing the gaps recovers the normalized marks. "
                        + "Lean checks the tree and table literals. Archive decoding and the "
                        + "construction of the equality certificates take place outside Lean."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("notik-real-golomb-minimizers"), ResolutionKind.Proved))), []));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Parenthesized(argument));

    private static Formula Minimum(Formula n, Formula t) =>
        Apply(Seq(Operatorname, Grp(F.Id("MinimumAt")), Sp), Seq(n, Comma, Sp, t));

    private static Formula Field(string name) => Seq(Mathbb, Grp(F.Id(name)));

    private static Formula Conjoin(Formula first, Formula second, Formula third) =>
        Seq(first, Sp, Land, Sp, second, Sp, Land, Sp, third);

    private static Formula Bind(Formula quantifier, string variable, Formula type) =>
        Seq(quantifier, Sp, F.Id(variable), Colon, Sp, type, Comma, Sp);

    private static Formula MinimumDefinition()
    {
        var n = F.Id("n");
        var t = F.Id("T");
        var x = F.Id("x");
        var z = F.Id("z");
        var i = F.Id("i");
        var reals = Field("R");
        var integers = Field("Z");
        var indices = Apply(Seq(Operatorname, Grp(F.Id("Fin")), Sp), Seq(n, Plus, D(1)));
        var realMarks = Seq(indices, Sp, To, Sp, reals);
        var integerMarks = Seq(indices, Sp, To, Sp, integers);
        var ruler = Apply(F.Id("G"), x);
        var length = Apply(F.Id("L"), x);
        var attainment = Parenthesized(Seq(Bind(Exists, "z", integerMarks), Conjoin(
            Equal(Apply(z, D(0)), D(0)),
            Equal(Apply(z, n), t),
            Apply(F.Id("G"), Apply(Iota, z)))));
        var lowerBound = Parenthesized(Seq(Bind(Forall, "x", realMarks),
            ruler, Sp, Implies, Sp, Apply(Iota, t), Sp, Leq, Sp, length));
        var equality = Parenthesized(Seq(Bind(Forall, "x", realMarks),
            Parenthesized(Conjoin(ruler, Equal(Apply(x, D(0)), D(0)), Equal(length, Apply(Iota, t)))),
            Sp, Implies, Sp, Bind(Forall, "i", indices), Bind(Exists, "z", integers),
            Equal(Apply(x, i), Apply(Iota, z))));
        return Disp(Seq(Bind(Forall, "n", Field("N")), Bind(Forall, "T", integers),
            Minimum(n, t), Sp, Iff, Sp, Conjoin(attainment, lowerBound, equality)));
    }
}
