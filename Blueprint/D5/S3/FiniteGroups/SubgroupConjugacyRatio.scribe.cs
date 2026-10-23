using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class SubgroupConjugacyRatioDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef LazorecTarnauceanu =
        LibraryNoteRef.Create("D5/L/FiniteGroups/lazorec2025subgroupconjugacy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Whole subgroup lattices and their inner-conjugacy quotients multiply over coprime products.",
        H("Subgroup Conjugacy Ratios"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("subgroup-conjugacy-observable"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubgroupConjugacyRatio.ratio"),
                H("The observable on actual groups"),
                StatementSource.FromAuthor(Observable()),
                AssessedProvenance.FromRepo(LazorecTarnauceanu),
                Blocks(Paragraph(Text(
                    "For a group G, latticeCount G is Nat.card (Subgroup G), including the "
                    + "trivial subgroup and G. SubgroupClasses G is the quotient of Subgroup G "
                    + "by the orbit relation for ConjAct G, acting by inner conjugation. "
                    + "classCount G is its Nat.card. The rational ratio divides these two "
                    + "cardinalities. On finite groups the denominator is positive, since "
                    + "the whole subgroup lattice contains the trivial subgroup. Section 1 "
                    + "of Lazorec and Tărnăuceanu defines this observable on finite groups. "
                    + "The displayed declaration defines a rational-valued function for any "
                    + "group; its interpretation here as the source ratio is on finite groups."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("subgroup-conjugacy-rational-attainment"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubgroupConjugacyRatio.RationalAttainment"),
                H("The exact rational attainment question"),
                StatementSource.FromAuthor(Target()),
                AssessedProvenance.FromLiterature(LazorecTarnauceanu),
                Blocks(Paragraph(Text(
                    "FiniteGroup packages an actual carrier, its group operation, and a proof "
                    + "of finiteness. The displayed proposition is Problem 4.1 in "
                    + "https://arxiv.org/html/2508.14267v2, in integer cross-multiplied form. "
                    + "It quantifies over every pair of integers with 1 ≤ a < b. "
                    + "The witness has no nilpotence, supersolvability, coprimality or supplied "
                    + "counting-formula assumption. This declaration defines the exact target; "
                    + "it does not prove its attainment."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("subgroup-conjugacy-coprime-product"),
                DeclarationHandle.Create(
                    "D5/S3/FiniteGroups/SubgroupConjugacyRatio.coprime_product_counts"),
                H("Coprime product multiplicativity"),
                StatementSource.FromAuthor(ProductCounts()),
                AssessedProvenance.FromRepo(LazorecTarnauceanu),
                Blocks(
                    Paragraph(Text(
                        "Let G and K be arbitrary finite groups whose orders are coprime. "
                        + "For every subgroup H of G × K and every (g,k) in H, taking powers "
                        + "first kills one component and then recovers the other using "
                        + "coprimality of its element order. Hence (g,1) and (1,k) belong to H. "
                        + "Conversely these two elements multiply to (g,k). Every subgroup "
                        + "is therefore exactly the product of its two projections.")),
                    Paragraph(Text(
                        "subgroupProductEquiv sends H to its projected subgroups, with inverse "
                        + "their direct product. Conjugation by (g,k) acts separately on the "
                        + "two factors. Products of subgroups are conjugate exactly when their "
                        + "corresponding factors are conjugate. classesProductEquiv consequently "
                        + "identifies the quotient of the full product lattice with the product "
                        + "of the two full subgroup-conjugacy quotients. Cardinalities of these "
                        + "bijections give both count identities, and rational division gives "
                        + "the third identity. The ratio identity is already stated in Section 1 "
                        + "of Lazorec and Tărnăuceanu; the displayed conjunction records the "
                        + "two separate count identities as well as that known consequence. "
                        + "No multiplicativity statement for noncoprime "
                        + "orders is asserted."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.Apply(F.Id(name), [.. xs]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Equal(Formula x, Formula y) => Seq(x, Eq, y);
    private static Formula Times(Formula x, Formula y) => Seq(x, Star, y);
    private static Formula Observable()
    {
        var g = F.Id("G");
        return Disp(All("G", F.Id("Typeu"), new Formula.TypeArrow(Call("Group", g),
            Equal(Call("ratio", g), Call("divide",
                Call("rationalCast", Call("classCount", g)),
                Call("rationalCast", Call("latticeCount", g)))))));
    }
    private static Formula Target()
    {
        var a = F.Id("a"); var b = F.Id("b"); var w = F.Id("W");
        var g = Call("Carrier", w);
        var equation = Equal(Times(b, Call("integerCast", Call("classCount", g))),
            Times(a, Call("integerCast", Call("latticeCount", g))));
        return Disp(Equal(Call("RationalAttainment"),
            All("a", F.Id("Integers"), All("b", F.Id("Integers"),
                new Formula.TypeArrow(Seq(D(1), Le, Sp, a),
                    new Formula.TypeArrow(Seq(a, Lt, b),
                        Ex("W", Call("FiniteGroup"), equation)))))));
    }
    private static Formula ProductCounts()
    {
        var g = F.Id("G"); var k = F.Id("K"); var product = Call("product", g, k);
        var body = Seq(
            Equal(Call("latticeCount", product),
                Times(Call("latticeCount", g), Call("latticeCount", k))),
            Land, Sp,
            Equal(Call("classCount", product),
                Times(Call("classCount", g), Call("classCount", k))),
            Land, Sp,
            Equal(Call("ratio", product), Times(Call("ratio", g), Call("ratio", k))));
        body = new Formula.TypeArrow(
            Call("Coprime", Call("card", g), Call("card", k)), body);
        body = new Formula.TypeArrow(Call("Finite", k), body);
        body = new Formula.TypeArrow(Call("Finite", g), body);
        body = new Formula.TypeArrow(Call("Group", k), body);
        body = new Formula.TypeArrow(Call("Group", g), body);
        return Disp(All("G", F.Id("Typeu"), All("K", F.Id("Typev"), body)));
    }
}
