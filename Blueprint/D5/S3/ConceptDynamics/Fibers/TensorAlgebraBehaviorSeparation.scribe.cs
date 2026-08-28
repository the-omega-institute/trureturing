using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Fibers;

internal sealed class TensorAlgebraBehaviorSeparationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Fibers/TensorAlgebraBehaviorSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An algebra tensor decomposition does not decide whether admitted behavior is a "
            + "product; constrained and unconstrained residue systems give the contrast.",
        H("Tensor Algebra and Behavior Products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("residue-admission-product-iff-coprime"),
                DeclarationHandle.Create(
                    Prefix + "joint_residue_admission_product_iff_coprime"),
                H("Residue admission is a product exactly for coprime moduli"),
                StatementSource.FromAuthor(ResidueCriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Behavior product is the named minimal test that the admitted pairs "
                            + "equal the product of their two marginal admission sets. Each "
                            + "marginal of the integer residue readout is the full local factor.")),
                    Paragraph(Text(
                        "The compatible joint image is therefore a behavior product exactly "
                            + "when it is the full direct product, which the reused FPOD 107.1 "
                            + "criterion identifies with coprimality. No primality is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tensor-algebra-does-not-force-behavior-product"),
                DeclarationHandle.Create(
                    Prefix
                        + "tensor_algebra_decomposition_does_not_force_behavior_product"),
                H("Tensor algebra decomposition does not force behavior decomposition"),
                StatementSource.FromAuthor(CounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The window M=6 has two prime-power factors, and the imported algebra "
                            + "factorization is bijective. Independently, the behavior state "
                            + "is a product and both its update and readout are identity maps.")),
                    Paragraph(Text(
                        "Its admitted pairs are the repeated modulus-two residue image. FPOD "
                            + "107.1 makes this a strict compatible subobject, so precisely the "
                            + "no-cross-factor-constraint premise fails and behavior is not a "
                            + "product. FPOD 107.1 itself contains no algebra statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("all-four-premises-behavior-product-control"),
                DeclarationHandle.Create(
                    Prefix + "all_four_premises_give_behavior_product_control"),
                H("All four premises yield the product control"),
                StatementSource.FromAuthor(ControlFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Keep the same two-factor M=6 algebra decomposition and use the "
                            + "coprime residue factors two and three. The product state, "
                            + "identity update, and identity readout meet the first three "
                            + "premises, while coprimality makes admission unrestricted.")),
                    Paragraph(Text(
                        "The behavior admission is consequently a product. The Lean audit "
                            + "also checks empty and singleton carriers, constant, identity, "
                            + "and zero maps, zero moduli, one tensor factor, and the one-by-one "
                            + "matrix algebra."))),
                DescribeRole.Theorem))));

    private static Formula Naturals() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula JointAdmission(Formula left, Formula right) =>
        new Formula.Subscript(F.Id("J"), Seq(left, Comma, Sp, right));

    private static Formula CallFormula(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(function), Open };
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

    private static Formula BehaviorProduct(Formula admission) =>
        CallFormula(F.Id("BehaviorProduct"), admission);

    private static Formula GcdOf(Formula left, Formula right) =>
        Seq(Gcd, Open, left, Comma, Sp, right, Close);

    private static Formula ResidueCriterionFormula()
    {
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        return Disp(Seq(
            Forall, Sp, m, Comma, Sp, n, Sp, InMacro, Sp, Naturals(), Comma,
            RowBreak, BehaviorProduct(JointAdmission(m, n)), Sp, Iff, Sp,
            GcdOf(m, n), Sp, Eq, Sp, D(1), Dot));
    }

    private static Formula CounterexampleFormula()
    {
        Formula window = D(6);
        Formula left = D(2);
        Formula right = D(2);
        Formula admission = JointAdmission(left, right);
        return Disp(Seq(
            CallFormula(F.Id("PrimeFactorCount"), window), Sp, Eq, Sp, D(2), Sp,
            Land, Sp, CallFormula(F.Id("TensorBijective"), window), Sp, Land, Sp,
            CallFormula(F.Id("ProductState"), left, right), Sp, Land, Sp,
            CallFormula(F.Id("FactorwiseUpdate"), left, right), Sp, Land, Sp,
            CallFormula(F.Id("FactorwiseReadout"), left, right), Sp, Land, Sp,
            Neg, CallFormula(F.Id("NoCrossConstraint"), admission), Sp, Land, Sp,
            Neg, BehaviorProduct(admission), Dot));
    }

    private static Formula ControlFormula()
    {
        Formula window = D(6);
        Formula left = D(2);
        Formula right = D(3);
        Formula admission = JointAdmission(left, right);
        return Disp(Seq(
            CallFormula(F.Id("PrimeFactorCount"), window), Sp, Eq, Sp, D(2), Sp,
            Land, Sp, CallFormula(F.Id("TensorBijective"), window), Sp, Land, Sp,
            CallFormula(F.Id("ProductState"), left, right), Sp, Land, Sp,
            CallFormula(F.Id("FactorwiseUpdate"), left, right), Sp, Land, Sp,
            CallFormula(F.Id("FactorwiseReadout"), left, right), Sp, Land, Sp,
            CallFormula(F.Id("NoCrossConstraint"), admission), Sp, Land, Sp,
            BehaviorProduct(admission), Dot));
    }
}
