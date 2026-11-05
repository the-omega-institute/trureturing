using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PackingDomatic;

internal sealed class PackingDomaticInfiniteSixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PackingDomatic/PackingDomaticInfiniteSix.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/bresar2026packingdomatic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The six-class packing-domatic palette of the two-way infinite path is exactly five.",
        H("Six Broadcast-Dominating Classes on the Infinite Path"),
        Blocks(
            Node("arbitrary-realization", "A common infinite realization", "Q", QFormula(),
                "The vertices of the two-way infinite path are all integers, with distance |u-v|. "
                + "Nat denotes the natural numbers, Int the integers, and Fin(6) the six labels 0 through 5. "
                + "Q(t) asks for a positive packing colouring f bounded by t and one class map c on the "
                + "same vertex set. Each of the six classes broadcast-dominates every integer: its "
                + "witness a covers x to radius f(a). Natural colour values are coerced to integers "
                + "in the distance comparisons. Neither map has a periodicity, measurability, "
                + "computability or colour-determined-class requirement.", DescribeRole.Definition),
            Node("exact-five", "The least palette is five", "result", ResultFormula(),
                "Theorem 3.6 of Brešar, Ferme and Hu supplies the five-colour upper construction: "
                + "the repeating colour pattern [5,1,2,4,1,3], starting with colour 5 at vertex 0. "
                + "Its class 0 consists of residues 1 and 4 modulo 6. Classes 1 through 5 have, "
                + "respectively, residues {0,8,15,23}, {2,9,17,24}, {3,11,18,26}, {5,12,20,27}, "
                + "and {6,14,21,29} modulo 30. This construction is the source's prior upper bound. "
                + "For each of the 30 residues and six classes, a checked finite certificate finds "
                + "a covering vertex at an offset from -5 through 5. Reduction modulo 30, together "
                + "with reduction modulo 6, transfers that certificate to every integer, including "
                + "negative vertices. Packing separation is proved for arbitrary pairs of integers. "
                + "For the lower bound, take any hypothetical Q(4) realization. Let J be the "
                + "integer interval [0,999] and I the interval [4,995]. Every x in I needs six "
                + "distinct covering vertices in J, since one class map assigns different labels "
                + "to its six witnesses. There are therefore at least 6 times 992 = 5952 "
                + "vertex-broadcast incidences. A vertex of colour j covers at most 2j+1 vertices. "
                + "For j equal to 2, 3 and 4, sending a vertex a of colour j to the integer "
                + "quotient a/(j+1) is injective, by strict packing separation. The resulting "
                + "colour-count bounds are 334, 250 and 200. Writing the total capacity as "
                + "3 times 1000 + 2 times N(2) + 4 times N(3) + 6 times N(4) bounds it by 5868, "
                + "contradicting 5952. This obstruction applies to arbitrary infinite realizations. "
                + "Increasing a palette bound preserves both maps, so exclusion at 4 excludes "
                + "every natural palette below 5. Together with attainment, this answers the "
                + "reader question immediately after Theorem 3.6 in Section 3.2: the exact value "
                + "of the six-class packing-domatic chromatic number of the two-way infinite "
                + "path is 5. This is a different question from the finite-path Problem 2.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bresar-ferme-hu-infinite-path-six-reader-question"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula QFormula()
    {
        var t = F.Id("t");
        var x = F.Id("x");
        var u = F.Id("u");
        var v = F.Id("v");
        var a = F.Id("a");
        var i = F.Id("i");
        var bounded = All("x", F.Id("Int"), And(Le(D(1), Call("f", x)), Le(Call("f", x), t)));
        var packing = All("u", F.Id("Int"), All("v", F.Id("Int"),
            Implies(Ne(u, v), Implies(Eq(Call("f", u), Call("f", v)),
                Lt(Call("f", u), Abs(Sub(u, v)))))));
        var dominating = All("x", F.Id("Int"), All("i", Call("Fin", D(6)),
            Ex("a", F.Id("Int"), And(Eq(Call("c", a), i), Le(Abs(Sub(x, a)), Call("f", a))))));
        return Disp(All("t", F.Id("Nat"), Iff(Call("Q", t),
            Ex("f", Arrow(F.Id("Int"), F.Id("Nat")),
                Ex("c", Arrow(F.Id("Int"), Call("Fin", D(6))),
                    And(bounded, And(packing, dominating)))))));
    }

    private static Formula ResultFormula() => Disp(And(Call("Q", D(5)),
        All("t", F.Id("Nat"), Implies(Call("Q", F.Id("t")), Le(D(5), F.Id("t"))))));

    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Abs(Formula a) => Seq(Lvert, Sp, a, Rvert, Sp);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
