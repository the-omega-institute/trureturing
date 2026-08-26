using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.PrimePowers;

internal sealed class CompatibleResidueJointImageDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two residue factors combine exactly along their common-modulus compatibility.",
        H("Compatible Residue Joint Image"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-residue-image-equals-compatible-pairs"),
                DeclarationHandle.Create(
                    Prefix + "joint_residue_image_eq_compatible_pairs"),
                H("The joint image is exactly the compatible-pair subobject"),
                StatementSource.FromAuthor(ImageFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary natural moduli m and n, an integer produces exactly "
                            + "those local residues whose integer representatives agree after "
                            + "reduction modulo gcd(m,n). No positivity or primality is used.")),
                    Paragraph(Text(
                        "The proof applies Nat.chineseRemainder' for nonzero moduli and treats "
                            + "each zero-modulus branch directly via ZMod integer casts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-residue-image-is-compatible-subobject"),
                DeclarationHandle.Create(
                    Prefix + "joint_residue_image_is_compatible_subobject"),
                H("Compatibility cuts the joint image out of the direct product"),
                StatementSource.FromAuthor(SubobjectFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The joint image is contained in the full direct product and equals the "
                        + "named compatibleResiduePairs set. Thus the inclusion is paired with "
                        + "the actual cross-factor equation that selects the subobject."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-residue-image-strict-subset-iff"),
                DeclarationHandle.Create(
                    Prefix + "joint_residue_image_ssubset_product_iff"),
                H("The compatible subobject is strict exactly for noncoprime moduli"),
                StatementSource.FromAuthor(StrictnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The pair of residues zero and one witnesses incompatibility whenever "
                        + "gcd(m,n) is not one. Conversely, gcd one makes the compatibility "
                        + "factor ZMod 1 a singleton, so every product pair is compatible."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("residue-realization-independent-iff-coprime"),
                DeclarationHandle.Create(
                    Prefix + "residue_realization_independent_iff_coprime"),
                H("Free realization occurs exactly for coprime moduli"),
                StatementSource.FromAuthor(IndependenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Surjectivity of the joint readout is equivalent to gcd(m,n)=1. Hence "
                        + "coprime factors fill the product, equal moduli do so only at modulus "
                        + "one, and a modulus-one factor imposes no restriction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "local-factorization-does-not-imply-realization-independence"),
                DeclarationHandle.Create(
                    Prefix
                        + "local_factorization_does_not_imply_realization_independence"),
                H("Local coverage does not imply independent joint realization"),
                StatementSource.FromAuthor(CounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each integer readout into ZMod 2 is surjective, but their repeated "
                            + "joint readout has only compatible pairs and cannot realize "
                            + "the product pair (0,1).")),
                    Paragraph(Text(
                        "The degenerate audit also covers inhabited carriers, modulus-zero "
                            + "identity readout, modulus-one constant readout, and the strict "
                            + "diagonal image at (0,0)."))),
                DescribeRole.Theorem))));

    private static Formula Naturals() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Indexed(Formula symbol, Formula m, Formula n) =>
        new Formula.Subscript(symbol, Seq(m, Comma, Sp, n));

    private static Formula JointImage(Formula m, Formula n) =>
        Indexed(F.Id("J"), m, n);

    private static Formula CompatiblePairs(Formula m, Formula n) =>
        Indexed(F.Id("C"), m, n);

    private static Formula ZModOf(Formula modulus) =>
        Seq(Operatorname, Grp(F.Id("ZMod")), Open, modulus, Close);

    private static Formula Product(Formula m, Formula n) =>
        Seq(ZModOf(m), Sp, Times, Sp, ZModOf(n));

    private static Formula GcdOf(Formula m, Formula n) =>
        Seq(Gcd, Open, m, Comma, Sp, n, Close);

    private static Formula Independent(Formula m, Formula n) =>
        Seq(Operatorname, Grp(F.Id("Independent")), Open, m, Comma, Sp, n, Close);

    private static Formula Readout(Formula modulus) =>
        new Formula.Subscript(F.Id("r"), modulus);

    private static Formula Surjective(Formula map) =>
        Seq(Operatorname, Grp(F.Id("Surjective")), Open, map, Close);

    private static Formula Quantified(Formula body)
    {
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        return Disp(Seq(
            Forall, Sp, m, Comma, Sp, n, Sp, InMacro, Sp, Naturals(), Comma,
            RowBreak, Grp(), body, Dot));
    }

    private static Formula ImageFormula()
    {
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        return Quantified(Seq(
            JointImage(m, n), Sp, Eq, Sp, CompatiblePairs(m, n)));
    }

    private static Formula SubobjectFormula()
    {
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        return Quantified(Seq(
            JointImage(m, n), Sp, Subseteq, Sp, Product(m, n), Sp, Land, Sp,
            JointImage(m, n), Sp, Eq, Sp, CompatiblePairs(m, n)));
    }

    private static Formula StrictnessFormula()
    {
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        return Quantified(Seq(
            JointImage(m, n), Sp, Subset, Sp, Product(m, n), Sp, Iff, Sp,
            GcdOf(m, n), Sp, Neq, Sp, D(1)));
    }

    private static Formula IndependenceFormula()
    {
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        return Quantified(Seq(
            Independent(m, n), Sp, Iff, Sp, GcdOf(m, n), Sp, Eq, Sp, D(1)));
    }

    private static Formula CounterexampleFormula() => Disp(Seq(
        Surjective(Readout(D(2))), Sp, Land, Sp,
        Surjective(Readout(D(2))), Sp, Land, Sp,
        Neg, Independent(D(2), D(2)), Dot));
}
