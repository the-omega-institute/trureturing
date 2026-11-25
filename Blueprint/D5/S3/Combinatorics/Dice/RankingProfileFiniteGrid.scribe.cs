using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Dice;

internal sealed class RankingProfileFiniteGridDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Convexity/bozokicsatotemesi2026dice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compression and closedness of the finite cubic ranking test.",
        H("Finite ranking profiles on an ordered grid"),
        Blocks(
            Definition("ranking-grid-support", "weightSupport", "Support of a finite weight",
                "The support consists of all labels where the weight is nonzero. Disjoint quantized ranges give disjoint supports in quantizedWeights_disjoint."),
            Definition("ranking-grid-probability", "IsProbability", "Finite probability weights",
                "Every weight is nonnegative and the sum over the finite carrier is one. The quantized marginals satisfy these conditions, and finiteWeightLaw_probability uses them to build a probability measure."),
            Definition("ranking-grid-mass", "rankMass", "Mass of a decreasing triple",
                "Sum the products a(x)b(y)c(z) over triples with z < y < x in the finite linear order. sum_rankTuples identifies this sum with a coordinate of the independent product law."),
            Definition("ranking-grid-profile", "profile", "Six cubic coordinates",
                "Apply the decreasing-triple sum to the three weight vectors in the orders XYZ, XZY, YXZ, YZX, ZXY, ZYX. quantizedProfile_eq and finiteProductLaw_realRankProfile use this order for the forward and reverse probability bridges."),
            Definition("ranking-profile-cubic-test", "finiteTest15", "The fifteen-label cubic test",
                "A profile passes when three probability weights on the same fifteen ordered labels, each with at most five positive entries, give its six cubic coordinates. finiteTest15_realizable uses the weights to form its finite product law.",
                FiniteTestFormula()),
            Theorem("ranking-grid-closed", "isClosed_finiteTest15", "Closedness of the cubic test",
                Call("IsClosed", Id("finiteTest15")),
                "The capped simplex is a finite union of compact coordinate faces. The cubic profile is continuous, so its image of the product of three capped simplexes is compact and closed. realRankProfile_mem_finiteTest15 uses closedness to pass to the quantization limit."),
            Theorem("ranking-grid-compression", "profile_mem_finiteTest15", "Compression from disjoint finite supports",
                CompressionFormula(),
                "For three probability weights on an arbitrary finite linear order, pairwise disjoint supports suffice for the profile to pass the test. With two weights fixed, two complementary block sums express two coordinates in terms of the other four. Carathéodory reduces the varying weight to at most five labels in its original support. Compress each role and relabel the union in increasing order. realRankProfile_mem_finiteTest15 applies this result at every quantization scale.")), []));

    private static DocumentBlock Definition(string id, string name, string title, string facts, Formula? formula = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(F.Disp(formula)),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(facts))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string id, string name, string title, Formula formula, string facts) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(F.Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(facts))), DescribeRole.Theorem);

    private static Formula Real => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Weights(Formula labels) => F.Seq(F.Open, labels, F.Sp, F.To, F.Sp, Real, F.Close);
    private static Formula.BoundVariable B(string name, Formula type) => new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula And(params Formula[] items) =>
        items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Member(Formula profile) =>
        new Formula.Relation(profile, FormulaRelationOperator.MemberOf, Id("finiteTest15"));
    private static Formula Disjoint(Formula a, Formula b) =>
        Call("Disjoint", Call("weightSupport", a), Call("weightSupport", b));

    private static Formula CompressionFormula()
    {
        Formula carrier = Id("A"), a = Id("a"), b = Id("b"), c = Id("c");
        Formula weights = Weights(carrier);
        Formula assumptions = And(Call("IsProbability", a), Call("IsProbability", b),
            Call("IsProbability", c), Disjoint(a, b), Disjoint(a, c), Disjoint(b, c));
        Formula implication = new Formula.Logic(assumptions, FormulaLogicOperator.Implies,
            Member(Call("profile", a, b, c)));
        Formula instances = F.Seq(F.OpenBracket, Call("Fintype", carrier), F.CloseBracket, F.Sp,
            F.OpenBracket, Call("LinearOrder", carrier), F.CloseBracket, F.Comma, F.Sp);
        return All(F.Seq(instances, All(implication, B("a", weights), B("b", weights), B("c", weights))),
            B("A", Id("Type")));
    }

    private static Formula FiniteTestFormula()
    {
        Formula labels = Call("Fin", Num(15)), weights = Weights(labels);
        Formula v = Id("v"), a = Id("a"), b = Id("b"), c = Id("c"), i = Id("i");
        Formula WithinCap(Formula p)
        {
            Formula positive = new Formula.Relation(Num(0), FormulaRelationOperator.LessThan,
                new Formula.Apply(p, [i]));
            Formula indices = F.Seq(F.OpenBrace, i, F.Colon, labels, F.Sp, F.Mid, F.Sp, positive, F.CloseBrace);
            return new Formula.Relation(Call("card", indices), FormulaRelationOperator.LessThanOrEqual, Num(5));
        }
        Formula witness = And(Call("IsProbability", a), Call("IsProbability", b), Call("IsProbability", c),
            WithinCap(a), WithinCap(b), WithinCap(c), Equal(Call("profile", a, b, c), v));
        Formula exists = new Formula.BindMany(FormulaQuantifier.Exists, [B("a", weights), B("b", weights), B("c", weights)], witness);
        return All(new Formula.Logic(Member(v), FormulaLogicOperator.Iff, exists), B("v", Weights(Call("Fin", Num(6)))));
    }
}
