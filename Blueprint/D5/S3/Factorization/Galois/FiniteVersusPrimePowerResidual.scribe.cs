using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class FiniteVersusPrimePowerResidualDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Galois/FiniteVersusPrimePowerResidual.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite residuals lie below prime-power residuals, and A5 makes this strict.",
        H("Finite and Prime-Power Residuals"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-residual-le-prime-power-residual"),
                DeclarationHandle.Create(
                    Prefix + "finite_residual_le_prime_power_residual"),
                H("All finite quotients leave a smaller kernel"),
                StatementSource.FromAuthor(InclusionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The prime-power quotient indices form a subfamily of all finite "
                        + "quotient indices. Intersecting the larger family of kernels can "
                        + "only decrease the residual."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("alternating-five-strict-residual-separation"),
                DeclarationHandle.Create(
                    Prefix + "alternating_five_strict_residual_separation"),
                H("A5 makes the inclusion strict"),
                StatementSource.FromAuthor(StrictFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For A5 the all-finite residual is trivial while the residual from all "
                        + "finite p-group quotients is the whole group."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("order-factorization-does-not-force-residual-equality"),
                DeclarationHandle.Create(
                    Prefix + "order_factorization_does_not_force_residual_equality"),
                H("Factoring the order does not decompose the quotients"),
                StatementSource.FromAuthor(OrderFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A5 has order 2^2 times 3 times 5, yet its two residuals differ. "
                        + "Lagrange and Sylow control orders and subgroups; they do not "
                        + "express a finite group as a limit of its p-group quotients."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("trivial-group-degenerate-case"),
                DeclarationHandle.Create(Prefix + "trivial_group_degenerate_case"),
                H("The trivial group gives equality"),
                StatementSource.FromAuthor(TrivialFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the one-element group both residuals are the bottom subgroup, so "
                        + "the general inclusion is equality and cannot be strict."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("p-group-residual-equality"),
                DeclarationHandle.Create(Prefix + "p_group_residual_equality"),
                H("A p-group supplies the extra structure for equality"),
                StatementSource.FromAuthor(PGroupFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If G is a p-group and p is prime, every finite quotient of G is again "
                        + "a p-group. Thus every all-finite kernel already occurs in the "
                        + "prime-power family. No finiteness assumption on G is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("alternating-five-simple-group-case"),
                DeclarationHandle.Create(
                    Prefix + "alternating_five_simple_group_case"),
                H("The finite simple case is maximally separated"),
                StatementSource.FromAuthor(SimpleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A5 is simple, its all-finite residual is bottom, its all-prime-power "
                        + "residual is top, and its joint prime-power observer is trivial."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("p-group-assumption-is-necessary"),
                DeclarationHandle.Create(Prefix + "p_group_assumption_is_necessary"),
                H("The p-group assumption cannot be removed"),
                StatementSource.FromAuthor(PGroupNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A5 is not a 2-group, while its finite and prime-power residuals "
                        + "are unequal. Thus primality alone does not imply equality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-parameter-is-necessary"),
                DeclarationHandle.Create(Prefix + "prime_parameter_is_necessary"),
                H("Primality cannot be removed"),
                StatementSource.FromAuthor(PrimeNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mathlib defines the raw IsPGroup predicate for every natural parameter. "
                        + "At the composite parameter 60, A5 satisfies that predicate but its "
                        + "finite and prime-power residuals remain unequal."))),
                DescribeRole.Theorem))));

    private static Formula Call(Formula function, params Formula[] arguments)
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

    private static Formula AlternatingFive() =>
        new Formula.Subscript(F.Id("A"), D(5));

    private static Formula FiniteResidual(Formula group) =>
        Call(F.Id("finiteResidual"), group);

    private static Formula PrimePowerResidual(Formula group) =>
        Call(F.Id("primePowerResidual"), group);

    private static Formula InclusionFormula()
    {
        Formula group = F.Id("G");
        return Disp(Seq(
            FiniteResidual(group), Sp, Le, Sp, PrimePowerResidual(group), Dot));
    }

    private static Formula StrictFormula()
    {
        Formula group = AlternatingFive();
        return Disp(Seq(
            FiniteResidual(group), Sp, Lt, Sp, PrimePowerResidual(group), Dot));
    }

    private static Formula OrderFormula()
    {
        Formula group = AlternatingFive();
        Formula order = Seq(
            D(2), Caret, Grp(D(2)), Sp, Times, Sp, D(3), Sp, Times, Sp, D(5));
        return Disp(Seq(
            Call(F.Id("card"), group), Sp, Eq, Sp, order, Sp, Land, Sp,
            FiniteResidual(group), Sp, Neq, Sp, PrimePowerResidual(group), Dot));
    }

    private static Formula TrivialFormula()
    {
        Formula group = Call(F.Id("trivialSubgroup"), AlternatingFive());
        Formula bottom = Call(F.Id("bottomSubgroup"), group);
        return Disp(Seq(
            FiniteResidual(group), Sp, Eq, Sp, bottom, Sp, Land, Sp,
            PrimePowerResidual(group), Sp, Eq, Sp, bottom, Sp, Land, Sp,
            Neg, Open, FiniteResidual(group), Sp, Lt, Sp,
            PrimePowerResidual(group), Close, Dot));
    }

    private static Formula PGroupFormula()
    {
        Formula prime = F.Id("p");
        Formula group = F.Id("G");
        return Disp(Seq(
            Call(F.Id("Prime"), prime), Sp, Land, Sp,
            Call(F.Id("IsPGroup"), prime, group), Sp, Rightarrow, Sp,
            FiniteResidual(group), Sp, Eq, Sp, PrimePowerResidual(group), Dot));
    }

    private static Formula SimpleFormula()
    {
        Formula group = AlternatingFive();
        Formula bottom = Call(F.Id("bottomSubgroup"), group);
        Formula top = Call(F.Id("topSubgroup"), group);
        return Disp(Seq(
            Call(F.Id("IsSimpleGroup"), group), Sp, Land, Sp,
            FiniteResidual(group), Sp, Eq, Sp, bottom, Sp, Land, Sp,
            PrimePowerResidual(group), Sp, Eq, Sp, top, Sp, Land, Sp,
            Call(F.Id("primePowerQuotientObserver"), group), Sp, Eq, Sp, D(1), Dot));
    }

    private static Formula PrimeNecessityFormula()
    {
        Formula group = AlternatingFive();
        return Disp(Seq(
            Neg, Call(F.Id("Prime"), D(6, 0)), Sp, Land, Sp,
            Call(F.Id("IsPGroup"), D(6, 0), group), Sp, Land, Sp,
            FiniteResidual(group), Sp, Neq, Sp, PrimePowerResidual(group), Dot));
    }

    private static Formula PGroupNecessityFormula()
    {
        Formula group = AlternatingFive();
        return Disp(Seq(
            Call(F.Id("Prime"), D(2)), Sp, Land, Sp,
            Neg, Call(F.Id("IsPGroup"), D(2), group), Sp, Land, Sp,
            FiniteResidual(group), Sp, Neq, Sp, PrimePowerResidual(group), Dot));
    }
}
