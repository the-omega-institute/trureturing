using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class OeisA375786CuboidMinimumVolumeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/OeisA375786CuboidMinimumVolume.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/huber2024a375786");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The smallest first edge, then the smallest second edge, gives minimum cuboid volume.",
        H("Huber's Minimum-Volume Cuboid Conjecture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a375786-cuboids"),
                DeclarationHandle.Create(Prefix + "cuboids"),
                H("Cuboids of a prescribed surface"),
                StatementSource.FromAuthor(CuboidsFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "OEIS A375786, NAME (unpaginated): \"a(n) is the minimum volume of an "
                    + "integer-sided cuboid having the same surface as a cube with edge length n.\" "
                    + "The triple p represents edges x = p.1, y = p.2.1 and z = p.2.2, "
                    + "ordered x ≤ y ≤ z. The equation xy + yz + xz = 3n² says the surface "
                    + "is 6n². Each positive edge is at most 3n², so the three inclusive "
                    + "intervals contain every such cuboid. Finset.product forms the "
                    + "right-associated product, and Finset.filter keeps the ordered solutions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a375786-volume"),
                DeclarationHandle.Create(Prefix + "volume"),
                H("Volume"),
                StatementSource.FromAuthor(VolumeFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "OEIS A375786, NAME (unpaginated): \"a(n) is the minimum volume of an "
                    + "integer-sided cuboid having the same surface as a cube with edge length n.\" "
                    + "The volume of the triple is the product of its three edge lengths."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a375786-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Huber's conjecture"),
                StatementSource.FromAuthor(Disp(Equivalent(F.Id("claim"), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "OEIS A375786, COMMENTS (unpaginated): \"Conjecture: From the integer-sided "
                    + "cuboids with same surface 6*n^2 always the one with the smallest edge length "
                    + "has the minimum volume. If there are several integer-sided cuboids having "
                    + "the smallest edge length, then the one with the smallest second smallest "
                    + "edge length has the minimum volume (checked up to a(1000)).\" "
                    + "Here n is any natural number at least one. The hypothesis on p chooses "
                    + "the least pair (p.1, p.2.1) in lexicographic order. The conclusion compares "
                    + "its volume with every member of the same finite set, using a non-strict inequality."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a375786-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The lexicographic minimum has minimum volume"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Write S = 3n². Ordered positive edges satisfy 3x² ≤ S and "
                    + "xS ≤ 2xyz + x³; hence x ≥ 3 forces xyz ≥ S. At x = 1 and n ≥ 2, "
                    + "the volume is strictly below S − 4. If no solution has first edge one, "
                    + "the explicit odd-n solution forces n to be even. Writing n = 2m then "
                    + "gives the solution (2, 2, 3m² − 1), of volume S − 4. With the first "
                    + "edge fixed, a smaller second edge gives no larger volume. These "
                    + "comparisons cover every competitor; n = 1 has only the unit cube."))),
                DescribeRole.Theorem))));

    private static Formula CuboidsFormula()
    {
        var n = F.Id("n");
        var p = F.Id("p");
        var bound = Multiply(D(3), new Formula.Power(n, D(2)));
        var interval = Call(Qualified("Finset", "Icc"), D(1), bound);
        var product = Call(Qualified("Finset", "product"), interval,
            Call(Qualified("Finset", "product"), interval, interval));
        var x = Projection(p, 1);
        var y = Projection(Projection(p, 2), 1);
        var z = Projection(Projection(p, 2), 2);
        var condition = And(Le(x, y), And(Le(y, z), Equal(
            Add(Add(Multiply(x, y), Multiply(y, z)), Multiply(x, z)), bound)));
        var predicate = Parenthesized(Seq(
            Operatorname, Grp(F.Id("fun")), Sp, p, Sp, Colon, Sp, TripleType(), Sp,
            Mapsto, Sp, Parenthesized(condition)));
        return Disp(All("n", Naturals(), Equal(Call(F.Id("cuboids"), n),
            Call(Qualified("Finset", "filter"), predicate, product))));
    }

    private static Formula VolumeFormula()
    {
        var p = F.Id("p");
        return Disp(All("p", TripleType(), Equal(Call(F.Id("volume"), p),
            Multiply(Multiply(Projection(p, 1), Projection(Projection(p, 2), 1)),
                Projection(Projection(p, 2), 2)))));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var p = F.Id("p");
        var q = F.Id("q");
        var set = Call(F.Id("cuboids"), n);
        var lex = All("q", TripleType(), Imply(Member(q, set),
            Or(Lt(Projection(p, 1), Projection(q, 1)),
                And(Equal(Projection(p, 1), Projection(q, 1)),
                    Le(Projection(Projection(p, 2), 1), Projection(Projection(q, 2), 1))))));
        var comparison = All("q", TripleType(), Imply(Member(q, set),
            Le(Call(F.Id("volume"), p), Call(F.Id("volume"), q))));
        return All("n", Naturals(), Imply(Le(D(1), n), All("p", TripleType(),
            Imply(Member(p, set), Imply(lex, comparison)))));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula TripleType() => Parenthesized(Seq(Naturals(), Sp, Times, Sp,
        Parenthesized(Seq(Naturals(), Sp, Times, Sp, Naturals()))));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Call(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Projection(Formula value, byte field) => Seq(value, Dot, D(field));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imply(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalent(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
}
