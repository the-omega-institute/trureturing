using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Gauss;

internal sealed class TarnauceanuImageDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/FiniteGroups/Gauss/TarnauceanuImage";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/tarnauceanu2026gauss");
    private static readonly LibraryNoteRef Earlier =
        LibraryNoteRef.Create("D5/L/FiniteGroups/fasolatarnauceanu2023gauss");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact Gauss values on C_(2^n) × C₂ rule out simultaneous closedness and discreteness in [1, ∞).",
        H("Tărnăuceanu’s Gauss image in the relative real topology"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gauss-invariant"),
                Handle("gauss"),
                H("The group-theoretical Gauss invariant"),
                StatementSource.FromAuthor(Invariant()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a finite group G the numerator sums the order of the full automorphism "
                    + "group of every actual subgroup H of G. The sum includes the trivial subgroup "
                    + "and G itself. Both the summands and the denominator are cast to the reals. "
                    + "This is the invariant in §1 of arXiv:2611.34371v1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gauss-cyclic-product"),
                Handle("Family"),
                H("The cyclic-product family"),
                StatementSource.FromAuthor(FamilyDefinition()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The exponent n ranges over the natural numbers. C with a subscript m "
                    + "denotes a cyclic group of order m. At n = 0 the group is cyclic. "
                    + "The exact value theorem below uses positive exponents."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gauss-cyclic-product-value"),
                Handle("gauss_family"),
                H("Exact values for all positive exponents"),
                StatementSource.FromAuthor(FamilyValue()),
                AssessedProvenance.FromRepo(Source, Earlier),
                Blocks(
                    Paragraph(Text(
                        "Each element determines the cyclic subgroup it generates. Fibers of this "
                        + "map count generators, and a finite cyclic subgroup has as many generators "
                        + "as full automorphisms. The cyclic contribution therefore equals the group order, "
                        + "as in Equation (1) and the earlier proof of Theorem 1.1.")),
                    Paragraph(Text(
                        "A subgroup with trivial intersection with the order-two projection kernel "
                        + "injects into the first cyclic factor and is cyclic. A noncyclic subgroup "
                        + "contains the kernel and is the full inverse image of a nontrivial subgroup "
                        + "of the first factor. There is exactly one actual noncyclic subgroup of "
                        + "type C_(2^k) × C₂ for each 1 ≤ k ≤ n.")),
                    Paragraph(Text(
                        "For k = 1 an automorphism is an ordered pair of distinct nonidentity "
                        + "images, giving six possibilities. For k ≥ 2 the image of the long generator "
                        + "has a generating first coordinate and arbitrary second coordinate. The image "
                        + "of the order-two generator has first coordinate killed by squaring and "
                        + "nonidentity second coordinate. These choices give 2^(k+1) automorphisms. "
                        + "The resulting real numerator from noncyclic subgroups is 4·2^n − 2, "
                        + "and the group order is 2·2^n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gauss-image"),
                Handle("gaussImage"),
                H("The image over all finite groups"),
                StatementSource.FromAuthor(Image()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The image lies in the real subtype [1, ∞). The cyclic contribution gives "
                    + "the lower bound 1. The domain of the range map is the type of bundled finite groups. Every finite "
                    + "group in any carrier universe has an isomorphic representative there, and a "
                    + "group isomorphism preserves the sum by transporting the actual subgroups and "
                    + "their automorphism groups."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gauss-image-conjunction-fails"),
                Handle("image_not_closed_and_discrete"),
                H("Remark 3.4, closedness and discreteness"),
                StatementSource.FromAuthor(Conclusion()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "This proves the negative answer to the alternative in Remark 3.4 "
                        + "(arXiv:2611.34371v1, p. 10). Closedness is in the subtype [1, ∞), "
                        + "and discreteness refers to the image with the topology induced from that subtype.")),
                    Paragraph(Text(
                        "The family values at exponents n + 1 converge to the relative point 3 "
                        + "and each differs from 3. Closedness would put 3 into the image. The sequence "
                        + "would then converge in the image itself, and the open singleton at 3 "
                        + "would have to contain every sufficiently late term."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("tarnauceanu-2026-gauss-image-closed-discrete"),
                    ResolutionKind.Proved)))));

    private static DeclarationHandle Handle(string name) =>
        DeclarationHandle.Create(Module + "." + name);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);

    private static Formula Named(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula Equals(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);

    private static Formula Cardinality(Formula value) => Seq(Vert, Sp, value, Sp, Vert);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula CyclicProduct(Formula n) =>
        Seq(F.Id("C"), Underscore, Grp(new Formula.Power(D(2), n)), Sp, Times, Sp,
            F.Id("C"), Underscore, Grp(D(2)));

    private static Formula Invariant()
    {
        var g = F.Id("G");
        var h = F.Id("H");
        var subgroup = Seq(h, Sp, Le, Sp, g);
        var sum = Seq(Sum, Underscore, Grp(subgroup), Sp, Cardinality(Named("Aut", h)));
        var finiteGroups = Seq(Operatorname, Grp(F.Id("FiniteGroup")));
        return Disp(All("G", finiteGroups,
            Equals(Call("f", g), new Formula.Fraction(sum, Cardinality(g)))));
    }

    private static Formula FamilyDefinition()
    {
        var n = F.Id("n");
        return Disp(All("n", Naturals(), Equals(Call("Family", n), CyclicProduct(n))));
    }

    private static Formula FamilyValue()
    {
        var n = F.Id("n");
        var premise = new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n);
        var value = Seq(D(3), Sp, Minus, Sp, new Formula.Power(D(2), Seq(Minus, n)));
        return Disp(All("n", Naturals(),
            new Formula.Logic(premise, FormulaLogicOperator.Implies,
                Equals(Call("f", CyclicProduct(n)), value))));
    }

    private static Formula RelativeSpace() => Seq(OpenBracket, D(1), Comma, Sp, Infty, Close);

    private static Formula Image() =>
        Disp(Seq(Equals(F.Id("I"), Named("Im", F.Id("f"))), Sp, Subseteq, Sp, RelativeSpace()));

    private static Formula Conclusion() =>
        Disp(new Formula.Not(new Formula.Logic(
            Named("IsClosed", F.Id("I")), FormulaLogicOperator.And,
            Named("DiscreteTopology", F.Id("I")))));
}
