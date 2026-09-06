using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Coding;

internal sealed class LeeBallTwoLatticeObstructionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction.";

    private static readonly LibraryNoteRef GravierMollardPayan =
        LibraryNoteRef.Create("D5/L/Arith/gravier1998lee");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three-dimensional radius-two Lee ball fails to inject into every "
            + "index-twenty-five lattice quotient.",
        H("Radius-Two Lee Ball Lattice Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lee-ball-two-definition"),
                DeclarationHandle.Create(Prefix + "leeBallTwo"),
                H("The complete radius-two Lee ball"),
                StatementSource.FromAuthor(LeeBallFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The definition lists all twenty-five integer triples in the "
                        + "three-dimensional radius-two Lee ball. The following membership "
                        + "theorem verifies that this finite enumeration is exactly the set "
                        + "cut out by the stated l1 inequality."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lee-ball-two-membership"),
                DeclarationHandle.Create(Prefix + "mem_leeBallTwo_iff"),
                H("Enumeration equals the Lee inequality"),
                StatementSource.FromAuthor(MembershipFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every listed point has l1 norm at most two, and a bounded integer "
                        + "case split proves that every triple satisfying the inequality "
                        + "occurs in the list."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lee-ball-two-cardinality"),
                DeclarationHandle.Create(Prefix + "leeBallTwo_card"),
                H("The ball has twenty-five points"),
                StatementSource.FromAuthor(CardinalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Kernel reduction checks the cardinality of the complete explicit "
                        + "enumeration; no native evaluator is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lee-ball-two-second-moment"),
                DeclarationHandle.Create(Prefix + "leeBallTwo_second_moment"),
                H("Second moment over ZMod 25"),
                StatementSource.FromAuthor(SecondMomentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each coefficient vector, every integer coordinate is reduced "
                        + "modulo twenty-five before multiplication. Expansion of the "
                        + "twenty-five terms gives eighteen times the coordinate-square sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lee-ball-two-fourth-moment"),
                DeclarationHandle.Create(Prefix + "leeBallTwo_fourth_moment"),
                H("Fourth moment over ZMod 25"),
                StatementSource.FromAuthor(FourthMomentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The fourth-power expansion separates into thirty times the fourth "
                        + "power sum and twelve times the square of the second power sum. "
                        + "All operations occur in ZMod 25."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zmod-twenty-five-readout"),
                DeclarationHandle.Create(Prefix + "zmod25_readout_not_injective"),
                H("The cyclic readout is never injective"),
                StatementSource.FromAuthor(ZModTwentyFiveReadoutFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Injectivity would identify the ball with all residues modulo "
                        + "twenty-five. The complete second and fourth residue moments then "
                        + "force a fourth-power sum congruent to four modulo five, while "
                        + "three fourth powers over F5 can sum only to zero, one, two, or three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zmod-five-pair-readout"),
                DeclarationHandle.Create(Prefix + "zmod5_pair_readout_not_injective"),
                H("The elementary readout is never injective"),
                StatementSource.FromAuthor(ZModFivePairReadoutFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every nonzero linear functional on F5 squared has five points in "
                        + "each fibre. Fibrewise summation and the second moment make the "
                        + "span of the two coefficient vectors totally isotropic. The "
                        + "explicit ternary F5 calculation then makes the vectors dependent, "
                        + "contradicting an injective paired readout."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("order-twenty-five-classification"),
                DeclarationHandle.Create(
                    Prefix + "addCommGroup_card_twenty_five_classification"),
                H("Classification of additive groups of order twenty-five"),
                StatementSource.FromAuthor(ClassificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The cyclic case is equivalent to ZMod 25. In the noncyclic case, "
                        + "exponent five supplies a ZMod 5 module; its cardinality forces "
                        + "finrank two and hence an additive equivalence with F5 squared."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lee-ball-two-lattice-obstruction"),
                DeclarationHandle.Create(Prefix + "leeBallTwo_lattice_obstruction"),
                H("No index-twenty-five lattice quotient separates the ball"),
                StatementSource.FromAuthor(LatticeObstructionFormula()),
                AssessedProvenance.FromLiterature(GravierMollardPayan),
                Blocks(
                    Paragraph(Text(
                        "The quotient has order twenty-five, so the classification sends it "
                            + "to either the cyclic or elementary readout obstruction. Thus "
                            + "two points of the radius-two Lee ball have the same quotient class.")),
                    Paragraph(Text(
                        "This module is an independent kernel-checked proof of the n = 3 "
                            + "lattice case proved by Gravier, Mollard, and Payan in 1998. "
                            + "Leung and Zhou proved the radius-two lattice result for every "
                            + "n at least three in 2020 (arXiv:1808.08520). The formal theorem "
                            + "asserts nothing about non-lattice tilings, other dimensions, "
                            + "or other radii; the cited papers are provenance rather than "
                            + "Lean proof dependencies. Literature attestation applies only "
                            + "to this lattice obstruction. The explicit ball enumeration, "
                            + "membership characterization, cardinality, moments, readout "
                            + "obstructions, and classification are independently derived "
                            + "proof ingredients in this repository."))),
                DescribeRole.Theorem))));

    private static Formula LeeBallFormula()
    {
        Formula[] points =
        [
            Tuple(-2, 0, 0),
            Tuple(-1, -1, 0), Tuple(-1, 0, -1), Tuple(-1, 0, 0),
            Tuple(-1, 0, 1), Tuple(-1, 1, 0),
            Tuple(0, -2, 0), Tuple(0, -1, -1), Tuple(0, -1, 0),
            Tuple(0, -1, 1), Tuple(0, 0, -2), Tuple(0, 0, -1),
            Tuple(0, 0, 0), Tuple(0, 0, 1), Tuple(0, 0, 2),
            Tuple(0, 1, -1), Tuple(0, 1, 0), Tuple(0, 1, 1), Tuple(0, 2, 0),
            Tuple(1, -1, 0), Tuple(1, 0, -1), Tuple(1, 0, 0),
            Tuple(1, 0, 1), Tuple(1, 1, 0), Tuple(2, 0, 0),
        ];
        return Disp(Seq(
            F.Id("leeBallTwo"), Sp, Eq, Sp, OpenBrace,
            Joined(points, Seq(Comma, Sp)), CloseBrace,
            Sp, Subseteq, Sp, IntegerCube(), Dot));
    }

    private static Formula MembershipFormula()
    {
        Formula x = F.Id("x");
        Formula x0 = Subscript(x, D(0));
        Formula x1 = Subscript(x, D(1));
        Formula x2 = Subscript(x, D(2));
        return Disp(Seq(
            Forall, Sp, x, Sp, InMacro, Sp, IntegerCube(), Comma, Sp,
            x, Sp, InMacro, Sp, F.Id("leeBallTwo"), Sp, Leftrightarrow, Sp,
            Abs(x0), Sp, Plus, Sp, Abs(x1), Sp, Plus, Sp, Abs(x2),
            Sp, Leq, Sp, D(2), Dot));
    }

    private static Formula CardinalityFormula() =>
        Disp(Seq(Card(F.Id("leeBallTwo")), Sp, Eq, Sp, D(2, 5), Dot));

    private static Formula SecondMomentFormula()
    {
        Formula a = F.Id("a");
        Formula x = F.Id("x");
        Formula i = F.Id("i");
        Formula dot = CoordinateDot(a, x, i, D(2, 5));
        return Disp(Seq(
            Forall, Sp, a, Colon, Sp, Arrow(FinThree(), ZMod(D(2, 5))), Comma, Sp,
            IndexedSum(Seq(x, Sp, InMacro, Sp, F.Id("leeBallTwo")), Power(Parenthesized(dot), D(2))),
            Sp, Eq, Sp, D(1, 8), Sp, Cdot, Sp,
            IndexedSum(Seq(i, Sp, InMacro, Sp, FinThree()), Power(Subscript(a, i), D(2))), Dot));
    }

    private static Formula FourthMomentFormula()
    {
        Formula a = F.Id("a");
        Formula x = F.Id("x");
        Formula i = F.Id("i");
        Formula dot = CoordinateDot(a, x, i, D(2, 5));
        Formula fourthSum = IndexedSum(
            Seq(i, Sp, InMacro, Sp, FinThree()), Power(Subscript(a, i), D(4)));
        Formula secondSum = IndexedSum(
            Seq(i, Sp, InMacro, Sp, FinThree()), Power(Subscript(a, i), D(2)));
        return Disp(Seq(
            Forall, Sp, a, Colon, Sp, Arrow(FinThree(), ZMod(D(2, 5))), Comma, Sp,
            IndexedSum(Seq(x, Sp, InMacro, Sp, F.Id("leeBallTwo")), Power(Parenthesized(dot), D(4))),
            Sp, Eq, Sp,
            D(3, 0), Sp, Cdot, Sp, fourthSum,
            Sp, Plus, Sp,
            D(1, 2), Sp, Cdot, Sp, Power(Parenthesized(secondSum), D(2)), Dot));
    }

    private static Formula ZModTwentyFiveReadoutFormula()
    {
        Formula a = F.Id("a");
        Formula x = F.Id("x");
        Formula i = F.Id("i");
        Formula readout = Seq(x, Sp, Mapsto, Sp, CoordinateDot(a, x, i, D(2, 5)));
        return Disp(Seq(
            Forall, Sp, a, Colon, Sp, Arrow(FinThree(), ZMod(D(2, 5))), Comma, Sp,
            Neg, Sp, Call("InjOn", Parenthesized(readout), F.Id("leeBallTwo")), Dot));
    }

    private static Formula ZModFivePairReadoutFormula()
    {
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula x = F.Id("x");
        Formula i = F.Id("i");
        Formula pair = Parenthesized(Seq(
            CoordinateDot(a, x, i, D(5)), Comma, Sp,
            CoordinateDot(b, x, i, D(5))));
        Formula readout = Seq(x, Sp, Mapsto, Sp, pair);
        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, b, Colon, Sp,
            Arrow(FinThree(), ZMod(D(5))), Comma, Sp,
            Neg, Sp, Call("InjOn", Parenthesized(readout), F.Id("leeBallTwo")), Dot));
    }

    private static Formula ClassificationFormula()
    {
        Formula group = F.Id("G");
        Formula cyclic = Call("Nonempty", AddEquiv(group, ZMod(D(2, 5))));
        Formula elementary = Call("Nonempty",
            AddEquiv(group, ProductType(ZMod(D(5)), ZMod(D(5)))));
        return Disp(Seq(
            Forall, Sp, group, Colon, Sp, F.Id("Type"), Comma, Sp,
            OpenBracket, Call("AddCommGroup", group), CloseBracket, Comma, Sp,
            Card(group), Sp, Eq, Sp, D(2, 5), Sp, Rightarrow, Sp,
            Parenthesized(Seq(cyclic, Sp, Lor, Sp, elementary)), Dot));
    }

    private static Formula LatticeObstructionFormula()
    {
        Formula lattice = F.Id("L");
        Formula quotient = Seq(IntegerCube(), Slash, lattice);
        Formula quotientMap = Parenthesized(Seq(
            F.Id("x"), Sp, Mapsto, Sp, OpenBracket, F.Id("x"), CloseBracket,
            Underscore, Grp(lattice)));
        return Disp(Seq(
            Forall, Sp, lattice, Colon, Sp, Call("AddSubgroup", IntegerCube()), Comma, Sp,
            Card(quotient), Sp, Eq, Sp, D(2, 5), Sp, Rightarrow, Sp,
            Neg, Sp, Call("InjOn", quotientMap, F.Id("leeBallTwo")), Dot));
    }

    private static Formula CoordinateDot(
        Formula coefficients, Formula point, Formula index, Formula modulus) =>
        IndexedSum(
            Seq(index, Sp, InMacro, Sp, FinThree()),
            Seq(Subscript(coefficients, index), Sp, Cdot, Sp,
                Residue(Subscript(point, index), modulus)));

    private static Formula Tuple(int x, int y, int z) =>
        Parenthesized(Seq(Integer(x), Comma, Sp, Integer(y), Comma, Sp, Integer(z)));

    private static Formula Integer(int value) => value < 0
        ? Seq(Minus, D((byte)(-value)))
        : D((byte)value);

    private static Formula FinThree() => Call("Fin", D(3));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula IntegerCube() => Power(Integers(), D(3));
    private static Formula ZMod(Formula modulus) => Call("ZMod", modulus);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);
    private static Formula ProductType(Formula left, Formula right) =>
        Seq(left, Sp, Times, Sp, right);
    private static Formula AddEquiv(Formula left, Formula right) =>
        Seq(left, Sp, Sim, Underscore, Grp(Plus), Sp, right);
    private static Formula Card(Formula value) =>
        Seq(Lvert, Sp, value, Sp, Rvert);
    private static Formula Abs(Formula value) =>
        Seq(Lvert, Sp, value, Sp, Rvert);
    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));
    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
    private static Formula Residue(Formula value, Formula modulus) =>
        Seq(OpenBracket, value, CloseBracket, Underscore, Grp(modulus));
    private static Formula IndexedSum(Formula index, Formula body) =>
        Seq(new Formula.Subscript(Sum, index), Sp, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Joined(Formula[] values, Formula separator)
    {
        List<Formula> items = [];
        for (int index = 0; index < values.Length; index++)
        {
            if (index > 0)
            {
                items.Add(separator);
            }
            items.Add(values[index]);
        }
        return Seq([.. items]);
    }
}
