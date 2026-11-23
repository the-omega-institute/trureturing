using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Algebra;

internal sealed class ChakrabortyPatraIdealZeroProductRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/Algebra/ChakrabortyPatraIdealZeroProductRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/chakrabortypatra2026idealzeroproduct");

    private static readonly Formula Ring = F.Id("R");
    private static readonly Formula K = F.Id("k");
    private static readonly Formula I = F.Id("I");
    private static readonly Formula Index = F.Id("i");
    private static readonly Formula Nat = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula Rat = Seq(Mathbb, Grp(F.Id("Q")));
    private static readonly Formula Ideals = Apply("Ideal", Ring);
    private static readonly Formula Probability = Seq(new Formula.Subscript(Zeta, K), Open, Ring, Close);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A binary square-zero extension refutes Chakraborty–Patra Conjecture 4.2.",
        H("Ideal zero-product probability does not characterize fields"),
        Blocks(
            Describe.Lean(DescribeId.Create("zero-product-probability"),
                DeclarationHandle.Create(Prefix + "zeta"), H("Ordered ideal zero-product probability"),
                StatementSource.FromAuthor(Disp(ProbabilityFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The numerator counts ordered tuples of actual ideals whose ideal product is the "
                    + "zero ideal. Repetitions, the zero ideal, and the unit ideal are included. "
                    + "For a finite carrier the ideals form a finite type because they inject into its "
                    + "power set. The zero ideal makes the denominator positive. The ratio is rational."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("field-criterion"),
                DeclarationHandle.Create(Prefix + "claim"), H("Chakraborty–Patra Conjecture 4.2"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The condition concerns one integer k at least two and the conclusion is that "
                    + "the given finite commutative ring with identity is a field. Proposition 4.1 "
                    + "of the same paper proves the field probability that motivates this converse."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("field-criterion-refuted"),
                DeclarationHandle.Create(Prefix + "result"), H("The universal field criterion is false"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Name("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take the eight-element square-zero extension of the binary field by its "
                        + "two-dimensional vector space. Every element with nonzero scalar part "
                        + "is a unit. Thus every proper ideal lies in the scalar projection kernel, "
                        + "where multiplication by a ring element acts through its scalar coordinate.")),
                    Paragraph(Text(
                        "The zero ideal, the three lines, the kernel, and the unit ideal give "
                        + "a bijection with the six actual ideals. The 25 ordered pairs of proper "
                        + "ideals have zero product. Of the pairs involving the unit ideal, exactly "
                        + "the two orders of zero and unit have zero product. The ordered sample "
                        + "therefore gives 27 of 36, or 3/4, at k = 2. The same ring contains a "
                        + "nonzero element with square zero and hence fails the field conclusion.")),
                    Paragraph(Text(
                        "Behboodi and Rakeei's Theorem 2.7 identifies the square-zero case of "
                        + "complete annihilating-ideal graphs. Adjacency accounts for products of "
                        + "distinct nonzero proper ideals. The ordered count here also uses the "
                        + "diagonal and the products involving zero and the unit ideal."))),
                DescribeRole.Theorem))));

    private static Formula ProbabilityFormula()
    {
        var tupleType = Seq(Apply("Fin", K), Sp, To, Sp, Ideals);
        var product = Seq(new Formula.Subscript(Prod,
            Seq(Index, InMacro, Apply("Fin", K))), Sp, new Formula.Apply(I, [Index]));
        var zeroTuples = Seq(OpenBrace, I, Colon, Sp, tupleType, Sp, Mid, Sp,
            Equal(product, Num(0)), CloseBrace);
        return Seq(Probability, Colon, Sp, Rat, Sp, Eq, Sp,
            new Formula.Fraction(Card(zeroTuples), new Formula.Power(Card(Ideals), K)));
    }

    private static Formula ClaimFormula() =>
        Seq(Forall, Sp, Open, Ring, Colon, Sp, Name("Type"), Close, Sp,
            Instance("CommRing"), Sp, Instance("Finite"), Sp,
            Open, K, Colon, Sp, Nat, Close, Comma, Sp,
            Num(2), Sp, Le, Sp, K, Sp, To, Sp,
            Equal(Probability, Subtract(Num(1),
                new Formula.Fraction(Num(1), new Formula.Power(Num(2), K)))),
            Sp, To, Sp, Apply("IsField", Ring));

    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Apply(string name, params Formula[] args) => new Formula.Apply(Name(name), [.. args]);
    private static Formula Instance(string name) => Seq(OpenBracket, Apply(name, Ring), CloseBracket);
    private static Formula Card(Formula value) => Seq(Lvert, value, Rvert);
}
