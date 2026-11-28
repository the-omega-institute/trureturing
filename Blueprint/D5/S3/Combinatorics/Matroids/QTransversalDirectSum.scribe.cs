using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class QTransversalDirectSumDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/QTransversalDirectSum";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/fulcher2026cyclicflatembedding");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The concatenated presentation computes the rank of the direct sum.",
        H("Direct sums of transversal q-matroids"),
        Blocks(
            Definition("splitCoordinates", "Coordinate splitting",
                "Split a vector indexed by Fin (m + n) into its first m and last n coordinates. "
                + "This linear equivalence identifies the combined coordinate space with the product of the two factor spaces."),
            Definition("firstProjection", "First projection",
                "Take the first factor after splitting the coordinates."),
            Definition("secondProjection", "Second projection",
                "Take the second factor after splitting the coordinates."),
            Definition("concatenatedPresentation", "Concatenated presentation",
                "Pull back every slot of the first family along the first projection, "
                + "then every slot of the second family along the second projection. "
                + "Under the coordinate equivalence the slots are the products of a first-family slot "
                + "with the entire second space and the entire first space with a second-family slot."),
            Describe.Lean(DescribeId.Create("fulcher-conjecture-four-eight"),
                DeclarationHandle.Create(Module + ".fulcher_conjecture_4_8"),
                H("Fulcher Conjecture 4.8"), StatementSource.FromAuthor(Disp(RankEquality())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The rank uses the original definition by dimensions of every-basis partial q-transversals. "
                        + "Each finite indexed family permits repetitions and can be empty. "
                        + "Both factor terms in the minimum use the same subspace W contained in U. "
                        + "The admissible costs are natural numbers and the set of costs contains the value at W = U, "
                        + "so its infimum is attained.")),
                    Paragraph(Text("The one-presentation Hall formula expresses rank as the minimum of the number "
                        + "of slots failing to contain a test subspace plus its codimension. "
                        + "For a common W, take a minimizing subspace in each projected space. "
                        + "Their joint preimage in W projects into both minimizers, with codimension "
                        + "at most the sum of the projected codimensions. "
                        + "In the other direction, use a minimizer for the concatenated presentation as W "
                        + "and bound each factor rank by the slot count at its full projected space."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("fulcher-2026-transversal-q-matroid-direct-sum"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string name, string label, string description) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(label),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(description))), DescribeRole.Definition);

    private static Formula RankEquality()
    {
        var f = F.Id("F");
        var m = F.Id("m");
        var n = F.Id("n");
        var k = F.Id("k");
        var ell = F.Id("l");
        var x = F.Id("X");
        var y = F.Id("Y");
        var u = F.Id("U");
        var w = F.Id("W");
        var d = F.Id("d");
        var combined = Subspace(Add(m, n));
        var first = Call("Submodule", "map", F.Id("firstProjection"), w);
        var second = Call("Submodule", "map", F.Id("secondProjection"), w);
        var cost = Add(Add(Apply(F.Id("qTransversalRank"), x, first), Apply(F.Id("qTransversalRank"), y, second)),
            Seq(Open, Call("Module", "finrank", f, u), Sp, Minus, Sp, Call("Module", "finrank", f, w), Close));
        var minimum = Apply(F.Id("sInf"), Seq(OpenBrace, d, Sp, Mid, Sp, Exists, Sp,
            Binder("W", combined), Comma, Sp,
            new Formula.Logic(Le(w, u), FormulaLogicOperator.And, Equal(d, cost)), CloseBrace));
        var rank = Apply(F.Id("qTransversalRank"), Apply(F.Id("concatenatedPresentation"), x, y), u);
        var families = All("X", new Formula.TypeArrow(Apply(F.Id("Fin"), k), Subspace(m)),
            All("Y", new Formula.TypeArrow(Apply(F.Id("Fin"), ell), Subspace(n)),
            All("U", combined, Equal(rank, minimum))));
        var dimensions = All("m", Naturals, All("n", Naturals, All("k", Naturals, All("l", Naturals, families))));
        return All("F", F.Id("Type"), Seq(OpenBracket, Apply(F.Id("Field"), f), CloseBracket, Sp,
            OpenBracket, Apply(F.Id("Fintype"), f), CloseBracket, Sp, dimensions));
    }

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Subspace(Formula n) =>
        Apply(F.Id("Submodule"), F.Id("F"), new Formula.TypeArrow(Apply(F.Id("Fin"), n), F.Id("F")));
    private static Formula Apply(Formula fn, params Formula[] arguments) => new Formula.Apply(fn, [.. arguments]);
    private static Formula Call(string owner, string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name))), arguments);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Binder(name, type), Comma, Sp, body);
    private static Formula Binder(string name, Formula type) => Seq(Open, F.Id(name), Colon, Sp, type, Close);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}
