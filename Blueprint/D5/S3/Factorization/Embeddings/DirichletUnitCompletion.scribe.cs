using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Embeddings;

internal sealed class DirichletUnitCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Embeddings/DirichletUnitCompletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dirichlet coordinates split unit recovery into a free lattice and finite torsion.",
        H("Dirichlet Unit Completion"),
        Blocks(
            Definition(
                "archimedean-lattice-coordinates",
                "ArchimedeanLatticeCoordinates",
                "Integer coordinates in the logarithmic unit lattice"),
            Definition(
                "unit-completion-coordinates",
                "UnitCompletionCoordinates",
                "Torsion and archimedean coordinates"),
            Definition(
                "unit-completion-reconstruction",
                "unitCompletionReconstruction",
                "Reconstruction from the two coordinate layers"),
            Theorem(
                "unit-rank-from-signature",
                "unit_rank_eq_real_add_complex_sub_one",
                "Unit rank is r1 plus r2 minus one",
                RankFormula(),
                "The number of infinite places is r1 plus r2. Mathlib's Dirichlet rank is "
                    + "one less than that count; no prime-distribution statement is used."),
            Theorem(
                "unit-completion-reconstruction-bijective",
                "unitCompletionReconstruction_bijective",
                "Two-layer reconstruction is bijective",
                ReconstructionFormula(),
                "Mathlib's unique Dirichlet decomposition supplies surjectivity and "
                    + "injectivity for the reconstruction homomorphism."),
            Definition(
                "unit-completion-multiplicative-equivalence",
                "unitCompletionMulEquiv",
                "The unit group as torsion times a free integer lattice"),
            Theorem(
                "rational-archimedean-signature",
                "rational_archimedean_signature",
                "The rational signature is one real and zero complex places",
                RationalSignatureFormula(),
                "The unique infinite place of the rationals is real, so the rational "
                    + "signature is exactly the pair one and zero."),
            Theorem(
                "rational-unit-rank-zero",
                "rational_unit_rank_zero",
                "The rational free unit rank vanishes",
                RationalRankFormula(),
                "Substitution of the rational signature into the rank formula leaves no "
                    + "free archimedean coordinate."),
            Theorem(
                "rational-torsion-is-sign",
                "rational_torsion_unit_eq_one_or_neg_one",
                "Rational torsion is exactly a sign choice",
                RationalTorsionFormula(),
                "Every rational root-of-unity coordinate is one or minus one. Thus the "
                    + "remaining torsion layer is a single sign bit."),
            Theorem(
                "rational-two-layer-recovery-iff-sign",
                "rational_two_layer_recovery_iff_sign",
                "Fixed finite data leaves exactly the sign bit",
                RationalRecoveryFormula(),
                "The concrete finite profile from section 178 fixes absolute value. Equality "
                    + "then becomes equivalent to equality of signs, including at zero."),
            Theorem(
                "imaginary-quadratic-unit-rank-zero",
                "imaginary_quadratic_unit_rank_zero",
                "Imaginary quadratic fields have unit rank zero",
                ImaginaryRankFormula(),
                "A signature with no real place and one complex pair gives rank zero."),
            Theorem(
                "imaginary-quadratic-units-are-torsion",
                "imaginary_quadratic_units_are_torsion",
                "Imaginary quadratic units are all torsion",
                ImaginaryTorsionFormula(),
                "The free product is indexed by an empty type, so every unit is its finite "
                    + "root-of-unity coordinate."),
            Theorem(
                "real-quadratic-unit-rank-one",
                "real_quadratic_unit_rank_one",
                "Real quadratic fields have unit rank one",
                RealRankFormula(),
                "Two real places and no complex pair give one free integer coordinate."),
            Definition(
                "real-quadratic-fundamental-unit",
                "realQuadraticFundamentalUnit",
                "The sole unit in the real quadratic fundamental system"),
            Theorem(
                "real-quadratic-unit-decomposition",
                "real_quadratic_unit_decomposition",
                "Real quadratic units are torsion times powers of one unit",
                RealDecompositionFormula(),
                "The rank-one fundamental system has one member. Every unit is therefore a "
                    + "root of unity times an integer power of this fundamental unit."))));

    private static DocumentBlock.Describe Definition(
        string id,
        string declaration,
        string heading) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(heading + "."))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        string heading,
        Formula formula,
        string explanation) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            DescribeRole.Theorem);

    private static Formula RankFormula()
    {
        Formula field = F.Id("K");
        return Disp(Seq(
            Apply(F.Id("rank"), field), Sp, Eq, Sp,
            Sub(F.Id("r"), D(1)), Open, field, Close, Sp, Plus, Sp,
            Sub(F.Id("r"), D(2)), Open, field, Close, Sp, Minus, Sp, D(1), Dot));
    }

    private static Formula ReconstructionFormula()
    {
        Formula field = F.Id("K");
        Formula source = Seq(
            Apply(F.Id("mu"), field), Sp, Times, Sp,
            Superscript(Integers(), Apply(F.Id("rank"), field)));
        return Disp(Seq(
            Apply(F.Id("Reconstruct"), field), Colon, Sp, source, Sp, To, Sp,
            Superscript(Apply(F.Id("O"), field), Times), Sp,
            F.Text, Grp(F.Id("is"), Sp, F.Id("bijective")), Dot));
    }

    private static Formula RationalSignatureFormula() =>
        Disp(Seq(
            Open, Sub(F.Id("r"), D(1)), Open, RationalNumbers(), Close, Comma, Sp,
            Sub(F.Id("r"), D(2)), Open, RationalNumbers(), Close, Close, Sp, Eq, Sp,
            Open, D(1), Comma, Sp, D(0), Close, Dot));

    private static Formula RationalRankFormula() =>
        Disp(Seq(Apply(F.Id("rank"), RationalNumbers()), Sp, Eq, Sp, D(0), Dot));

    private static Formula RationalTorsionFormula()
    {
        Formula root = F.Id("zeta");
        return Disp(Seq(
            Forall, Sp, root, Sp, InMacro, Sp, Apply(F.Id("mu"), RationalNumbers()), Comma, Sp,
            root, Sp, Eq, Sp, D(1), Sp, Lor, Sp, root, Sp, Eq, Sp, Minus, D(1), Dot));
    }

    private static Formula RationalRecoveryFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula sameProfile = Seq(Profile(x), Sp, Eq, Sp, Profile(y));
        return Disp(Seq(
            Forall, Sp, x, Comma, Sp, y, Sp, InMacro, Sp, RationalNumbers(), Comma, Sp,
            sameProfile, Sp, Rightarrow, Sp, Open,
            x, Sp, Eq, Sp, y, Sp, Iff, Sp,
            Sign(x), Sp, Eq, Sp, Sign(y), Close, Dot));
    }

    private static Formula ImaginaryRankFormula()
    {
        Formula field = F.Id("K");
        Formula signature = Seq(
            Sub(F.Id("r"), D(1)), Open, field, Close, Sp, Eq, Sp, D(0), Sp, Land, Sp,
            Sub(F.Id("r"), D(2)), Open, field, Close, Sp, Eq, Sp, D(1));
        return Disp(Seq(signature, Sp, Rightarrow, Sp,
            Apply(F.Id("rank"), field), Sp, Eq, Sp, D(0), Dot));
    }

    private static Formula ImaginaryTorsionFormula()
    {
        Formula field = F.Id("K");
        Formula unit = F.Id("u");
        return Disp(Seq(
            Open, Sub(F.Id("r"), D(1)), Open, field, Close, Comma, Sp,
            Sub(F.Id("r"), D(2)), Open, field, Close, Close, Sp, Eq, Sp,
            Open, D(0), Comma, Sp, D(1), Close, Sp, Rightarrow, Sp,
            Forall, Sp, unit, Sp, InMacro, Sp,
            Superscript(Apply(F.Id("O"), field), Times), Comma, Sp,
            unit, Sp, InMacro, Sp, Apply(F.Id("mu"), field), Dot));
    }

    private static Formula RealRankFormula()
    {
        Formula field = F.Id("K");
        Formula signature = Seq(
            Sub(F.Id("r"), D(1)), Open, field, Close, Sp, Eq, Sp, D(2), Sp, Land, Sp,
            Sub(F.Id("r"), D(2)), Open, field, Close, Sp, Eq, Sp, D(0));
        return Disp(Seq(signature, Sp, Rightarrow, Sp,
            Apply(F.Id("rank"), field), Sp, Eq, Sp, D(1), Dot));
    }

    private static Formula RealDecompositionFormula()
    {
        Formula field = F.Id("K");
        Formula unit = F.Id("u");
        Formula root = F.Id("zeta");
        Formula exponent = F.Id("n");
        Formula epsilon = F.Id("epsilon");
        return Disp(Seq(
            Open, Sub(F.Id("r"), D(1)), Open, field, Close, Comma, Sp,
            Sub(F.Id("r"), D(2)), Open, field, Close, Close, Sp, Eq, Sp,
            Open, D(2), Comma, Sp, D(0), Close, Sp, Rightarrow, Sp,
            Forall, Sp, unit, Comma, Sp, Exists, Sp, root, Sp, InMacro, Sp,
            Apply(F.Id("mu"), field), Comma, Sp, Exists, Sp, exponent, Sp, InMacro, Sp,
            Integers(), Comma, Sp, unit, Sp, Eq, Sp, root, Sp, Times, Sp,
            Superscript(epsilon, exponent), Dot));
    }

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, index);

    private static Formula Superscript(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Profile(Formula value) =>
        Apply(F.Id("nu"), value);

    private static Formula Sign(Formula value) =>
        Seq(Operatorname, Grp(F.Id("sgn")), Open, value, Close);

    private static Formula Integers() =>
        Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula RationalNumbers() =>
        Seq(Mathbb, Grp(F.Id("Q")));
}
