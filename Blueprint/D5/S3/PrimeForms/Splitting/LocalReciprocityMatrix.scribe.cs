using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Splitting;

internal sealed class LocalReciprocityMatrixDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The odd-prime reciprocity matrix has distinct row and column collision relations.",
        H("Local Reciprocity Matrix and Its Two Reading Directions"),
        Blocks(
            DefinitionNode(
                "odd-prime-index-space",
                "OddPrime",
                "Odd-prime index space",
                "The observer coordinate consists of natural primes other than two."),
            DefinitionNode(
                "discriminant-coordinate-space",
                "Discriminant",
                "Discriminant coordinate space",
                "Discriminant coordinates are integer values, including zero and one."),
            DefinitionNode(
                "local-reciprocity-matrix",
                "localReciprocityMatrix",
                "Local reciprocity matrix",
                "The entry at an odd prime and discriminant is the Legendre symbol."),
            DefinitionNode(
                "prime-observes-discriminants",
                "primeObservesDiscriminants",
                "A prime observes discriminants",
                "Fixing the prime produces the row map from discriminants to readings."),
            DefinitionNode(
                "discriminant-observes-primes",
                "discriminantObservesPrimes",
                "A discriminant observes primes",
                "Fixing the discriminant produces the column map from primes to readings."),
            DefinitionNode(
                "same-at-prime",
                "SameAtPrime",
                "Row indistinguishability",
                "Two discriminants are row-indistinguishable when one prime reads them equally."),
            DefinitionNode(
                "same-at-discriminant",
                "SameAtDiscriminant",
                "Column indistinguishability",
                "Two primes are column-indistinguishable when one discriminant reads them "
                    + "equally."),
            DefinitionNode(
                "split-at-prime",
                "IsSplitAt",
                "Split reading",
                "The split predicate is the decidable condition that the entry equals one."),
            DefinitionNode(
                "inert-at-prime",
                "IsInertAt",
                "Inert reading",
                "The inert predicate is the decidable condition that the entry equals minus one."),
            DefinitionNode(
                "ramified-at-prime",
                "IsRamifiedAt",
                "Ramified reading",
                "The ramified predicate is the decidable condition that the entry equals zero."),
            Describe.Lean(
                DescribeId.Create("local-reciprocity-value-trichotomy"),
                Handle("local_reciprocity_value_trichotomy"),
                H("Every matrix entry has one of three values"),
                StatementSource.FromAuthor(ValueTrichotomyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Legendre character dichotomy away from zero and its exact zero "
                        + "criterion place every entry in the set consisting of minus one, "
                        + "zero, and one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("split-iff-nonzero-square-mod-prime"),
                Handle("split_iff_nonzero_square_mod_prime"),
                H("Split means nonzero square"),
                StatementSource.FromAuthor(SplitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An entry is split exactly when the discriminant is a nonzero square "
                        + "modulo the fixed prime."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("inert-iff-nonsquare-mod-prime"),
                Handle("inert_iff_nonsquare_mod_prime"),
                H("Inert means nonsquare"),
                StatementSource.FromAuthor(InertFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An entry is inert exactly when the discriminant is not a square modulo "
                        + "the fixed prime."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ramified-iff-prime-divides-discriminant"),
                Handle("ramified_iff_prime_dvd_discriminant"),
                H("Ramified means divisibility"),
                StatementSource.FromAuthor(RamifiedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exact zero criterion identifies ramification with divisibility of "
                        + "the discriminant by the fixed prime."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("row-reading-collision-at-three"),
                Handle("row_reading_collision_at_three"),
                H("A fixed row has a collision"),
                StatementSource.FromAuthor(RowCollisionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The distinct discriminants five and eight both have inert reading at "
                        + "the fixed prime three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("column-reading-collision-at-five"),
                Handle("column_reading_collision_at_five"),
                H("A fixed column has a collision"),
                StatementSource.FromAuthor(ColumnCollisionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The distinct primes three and seven both have inert reading at the "
                        + "fixed discriminant five."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reciprocity-does-not-identify-reading-directions"),
                Handle("reciprocity_does_not_identify_reading_directions"),
                H("Reciprocity does not identify the two axes"),
                StatementSource.FromAuthor(DirectionSeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Quadratic reciprocity equates the transposed cells at five and thirteen. "
                        + "Nevertheless, five and eight collide in the row at three while "
                        + "three and five are separated in the column at five."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discriminant-degeneracy-audit"),
                Handle("discriminant_degeneracy_audit"),
                H("Degenerate discriminants are explicit"),
                StatementSource.FromAuthor(DegeneracyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Zero gives a constant ramified column and one gives a constant split "
                        + "column. At three, square four splits while divisible square nine "
                        + "ramifies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("primality-is-necessary-for-ramified-iff"),
                Handle("primality_is_necessary_for_ramified_iff"),
                H("Primality is necessary for the divisibility reading"),
                StatementSource.FromAuthor(PrimalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At composite Jacobi index nine, numerator three gives zero although "
                        + "nine does not divide three. Dropping primality breaks the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("oddness-is-necessary-for-inert-value"),
                Handle("oddness_is_necessary_for_inert_value"),
                H("The prime two has no inert value"),
                StatementSource.FromAuthor(OddnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the prime two every nonzero class is a square, so its Legendre symbol "
                        + "never takes the inert value minus one."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) =>
        DeclarationHandle.Create(Prefix + name);

    private static DocumentBlock.Describe DefinitionNode(
        string id,
        string declaration,
        string heading,
        string text) =>
        Describe.Lean(
            DescribeId.Create(id),
            Handle(declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            DescribeRole.Definition);

    private static Formula Matrix(Formula prime, Formula discriminant) =>
        Call("localReciprocityMatrix", prime, discriminant);

    private static Formula ValueTrichotomyFormula()
    {
        Formula prime = F.Id("p");
        Formula discriminant = F.Id("Delta");
        return Disp(Seq(
            Matrix(prime, discriminant), Sp, InMacro, Sp, OpenBrace,
            Minus, D(1), Comma, Sp, D(0), Comma, Sp, D(1), CloseBrace, Dot));
    }

    private static Formula SplitFormula()
    {
        Formula prime = F.Id("p");
        Formula discriminant = F.Id("Delta");
        return Disp(Seq(
            Call("IsSplitAt", prime, discriminant), Sp, Iff, Sp,
            Call("NeqMod", discriminant, D(0), prime), Sp, Land, Sp,
            Call("IsSquareMod", discriminant, prime), Dot));
    }

    private static Formula InertFormula()
    {
        Formula prime = F.Id("p");
        Formula discriminant = F.Id("Delta");
        return Disp(Seq(
            Call("IsInertAt", prime, discriminant), Sp, Iff, Sp,
            Neg, Call("IsSquareMod", discriminant, prime), Dot));
    }

    private static Formula RamifiedFormula()
    {
        Formula prime = F.Id("p");
        Formula discriminant = F.Id("Delta");
        return Disp(Seq(
            Call("IsRamifiedAt", prime, discriminant), Sp, Iff, Sp,
            Call("Dvd", prime, discriminant), Dot));
    }

    private static Formula RowCollisionFormula() => Disp(Seq(
        D(5), Sp, Neq, Sp, D(8), Sp, Land, RowBreak,
        Matrix(D(3), D(5)), Sp, Eq, Sp, Matrix(D(3), D(8)), Dot));

    private static Formula ColumnCollisionFormula() => Disp(Seq(
        D(3), Sp, Neq, Sp, D(7), Sp, Land, RowBreak,
        Matrix(D(3), D(5)), Sp, Eq, Sp, Matrix(D(7), D(5)), Dot));

    private static Formula DirectionSeparationFormula() => Disp(Seq(
        Matrix(D(5), D(1, 3)), Sp, Eq, Sp, Matrix(D(1, 3), D(5)), Sp, Land, RowBreak,
        Matrix(D(3), D(5)), Sp, Eq, Sp, Matrix(D(3), D(8)), Sp, Land, RowBreak,
        Neg, Open, Matrix(D(3), D(5)), Sp, Eq, Sp, Matrix(D(5), D(5)), Close, Dot));

    private static Formula DegeneracyFormula()
    {
        Formula prime = F.Id("p");
        return Disp(Seq(
            Open, Forall, Sp, prime, Colon, Sp, F.Id("OddPrime"), Comma, Sp,
            Matrix(prime, D(0)), Sp, Eq, Sp, D(0), Sp, Land, Sp,
            Matrix(prime, D(1)), Sp, Eq, Sp, D(1), Close, Sp, Land, RowBreak,
            Matrix(D(3), D(4)), Sp, Eq, Sp, D(1), Sp, Land, RowBreak,
            Matrix(D(3), D(9)), Sp, Eq, Sp, D(0), Dot));
    }

    private static Formula PrimalityFormula() => Disp(Seq(
        Call("jacobiSym", D(3), D(9)), Sp, Eq, Sp, D(0), Sp, Land, Sp,
        Neg, Call("Dvd", D(9), D(3)), Dot));

    private static Formula OddnessFormula()
    {
        Formula discriminant = F.Id("Delta");
        return Disp(Seq(
            Forall, Sp, discriminant, Colon, Sp, F.Id("Z"), Comma, Sp,
            Call("legendreSym", D(2), discriminant), Sp, Neq, Sp,
            Minus, D(1), Dot));
    }
}
