using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.IdealClassGroups;

internal sealed class IdealIdentityPrincipalityGeneratorLayersDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Factorization/IdealClassGroups/"
        + "IdealIdentityPrincipalityGeneratorLayers.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime valuations identify an ideal, the class group detects principality, and a "
            + "unit coordinate relative to a nonzero generator identifies the exact generator.",
        H("Ideal Identity, Principality, and Generator Coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-valuations-recover-the-fractional-ideal"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "ideal_valuation_layer_recovers_fractional_ideal"),
                H("All prime-ideal valuations recover the fractional ideal"),
                StatementSource.FromAuthor(ValuationRecoveryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is a direct reuse of the existing D5 faithfulness theorem; no "
                        + "factorization or injectivity argument is repeated here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-class-group-detects-principality"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "class_group_layer_detects_principality"),
                H("The trivial class is exactly the principal locus"),
                StatementSource.FromAuthor(PrincipalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The imported principal-ideal criterion separates knowing an ideal from "
                        + "knowing that it admits a global generator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("an-identified-ideal-need-not-be-principal"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "identified_ideal_need_not_be_principal"),
                H("Ideal identity does not imply principality"),
                StatementSource.FromAuthor(IdentifiedNonprincipalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The named norm-two ideal in the quadratic order is already completely "
                        + "identified and principal at every nonzero-prime localization, yet "
                        + "the imported local-global theorem proves it is not principal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-pid-has-no-nonprincipal-ideal-witness"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "nontrivial_class_group_is_necessary"),
                H("The first strictness disappears in a PID"),
                StatementSource.FromAuthor(PidDegeneracyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every ideal of the integers is principal, so the nonprincipal-ideal "
                        + "witness necessarily depends on leaving the trivial-class-group case."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-principal-ideal-has-distinct-generators"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "principality_does_not_determine_generator"),
                H("Principality does not choose a generator"),
                StatementSource.FromAuthor(DistinctGeneratorsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integers one and minus one are distinct associates and generate the "
                        + "same ideal. The proof uses Mathlib's singleton-span theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-trivial-unit-group-has-no-coordinate-strictness"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "nontrivial_unit_is_necessary"),
                H("Distinct unit coordinates require a nontrivial unit group"),
                StatementSource.FromAuthor(TrivialUnitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The unit group of ZMod two is a singleton. This concrete audit records the "
                        + "degenerate case in which the second strictness witness cannot exist."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unit-coordinates-preserve-the-principal-ideal"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "unit_coordinate_preserves_principal_ideal"),
                H("Changing the unit coordinate preserves the ideal"),
                StatementSource.FromAuthor(UnitPreservationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiplication by a unit uses Mathlib's exact singleton-span lemma and "
                        + "needs only a commutative semiring, not a field or a domain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ideal-plus-unit-coordinate-recovers-the-generator"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "ideal_and_unit_coordinate_recover_generator"),
                H("The ideal and unit coordinate recover the exact generator"),
                StatementSource.FromAuthor(UnitRecoveryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equal singleton spans first yield associated generators. A nonzero base in "
                        + "a domain then cancels, making the associated unit coordinate unique."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-generators-destroy-coordinate-uniqueness"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "nonzero_generator_is_necessary"),
                H("A zero generator cannot have a unique unit coordinate"),
                StatementSource.FromAuthor(ZeroGeneratorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Over the integers, both unit coordinates one and minus one send the zero "
                        + "base to zero. Thus the nonzero-base hypothesis is necessary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-divisors-destroy-coordinate-uniqueness"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "no_zero_divisors_is_necessary"),
                H("A nonzero zero divisor can have a unit stabilizer"),
                StatementSource.FromAuthor(ZeroDivisorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In ZMod eight, the nonzero element four is fixed by both unit coordinates "
                        + "one and minus one. Nonzeroness alone therefore cannot replace the "
                        + "domain condition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-zero-carrier-is-nonempty"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "zero_carrier_is_not_empty"),
                H("A zero element excludes the empty carrier"),
                StatementSource.FromAuthor(NonemptyCarrierFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The empty-type audit is definitional: the structure supplies its zero "
                        + "element. There is no natural-number parameter to audit at zero."))),
                DescribeRole.Theorem))));

    private static Formula Span(Formula value) => Call("IdealSpan", value);

    private static Formula UnitAction(Formula basis, Formula coordinate) =>
        Call("UnitAction", basis, coordinate);

    private static Formula Valuation(Formula prime, Formula ideal) =>
        Call("valuation", prime, ideal);

    private static Formula ValuationRecoveryFormula()
    {
        Formula left = F.Id("I");
        Formula right = F.Id("J");
        Formula prime = F.Id("p");
        return Disp(Seq(
            Forall, Sp, left, Comma, Sp, right, Comma, RowBreak, Grp(),
            Open, Forall, Sp, prime, Comma, Sp,
            Valuation(prime, left), Sp, Eq, Sp, Valuation(prime, right), Close,
            Sp, Rightarrow, Sp, left, Sp, Eq, Sp, right, Dot));
    }

    private static Formula PrincipalityFormula()
    {
        Formula ideal = F.Id("I");
        return Disp(Seq(
            Call("IsPrincipal", ideal), Sp, Iff, Sp,
            Call("ClassGroupMk", ideal), Sp, Eq, Sp, D(1), Dot));
    }

    private static Formula IdentifiedNonprincipalFormula()
    {
        Formula ideal = F.Id("I");
        return Disp(Seq(
            Exists, Sp, ideal, Colon, Sp, Call("Ideal", F.Id("QuadraticOrder")), Comma,
            Sp, ideal, Sp, Eq, Sp, F.Id("normTwoIdeal"), Sp, Land, Sp,
            Call("LocallyPrincipal", ideal), Sp, Land, Sp,
            Neg, Sp, Call("IsPrincipal", ideal), Dot));
    }

    private static Formula PidDegeneracyFormula()
    {
        Formula ideal = F.Id("I");
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        return Disp(Seq(
            Neg, Sp, Exists, Sp, ideal, Colon, Sp, Call("Ideal", integers), Comma,
            Sp, Neg, Sp, Call("IsPrincipal", ideal), Dot));
    }

    private static Formula DistinctGeneratorsFormula()
    {
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        return Disp(Seq(
            Exists, Sp, left, Comma, Sp, right, InMacro, Sp, integers, Comma, Sp,
            left, Sp, Neq, Sp, right, Sp, Land, Sp,
            Span(left), Sp, Eq, Sp, Span(right), Dot));
    }

    private static Formula TrivialUnitFormula()
    {
        Formula coordinate = F.Id("u");
        Formula units = Call("Units", Call("ZMod", D(2)));
        return Disp(Seq(
            Neg, Sp, Exists, Sp, coordinate, Colon, Sp, units, Comma, Sp,
            coordinate, Sp, Neq, Sp, D(1), Dot));
    }

    private static Formula UnitPreservationFormula()
    {
        Formula basis = F.Id("a");
        Formula coordinate = F.Id("u");
        return Disp(Seq(
            Forall, Sp, basis, Comma, Sp, coordinate, Comma, Sp,
            Span(UnitAction(basis, coordinate)), Sp, Eq, Sp, Span(basis), Dot));
    }

    private static Formula UnitRecoveryFormula()
    {
        Formula basis = F.Id("a");
        Formula target = F.Id("b");
        Formula coordinate = F.Id("u");
        return Disp(Seq(
            basis, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            Span(target), Sp, Eq, Sp, Span(basis), Sp, Rightarrow, RowBreak, Grp(),
            Exists, Bang, Sp, coordinate, Comma, Sp,
            UnitAction(basis, coordinate), Sp, Eq, Sp, target, Dot));
    }

    private static Formula ZeroGeneratorFormula()
    {
        Formula coordinate = F.Id("u");
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        return Disp(Seq(
            Neg, Sp, Exists, Bang, Sp, coordinate, Colon, Sp,
            Call("Units", integers), Comma, Sp,
            UnitAction(D(0), coordinate), Sp, Eq, Sp, D(0), Dot));
    }

    private static Formula ZeroDivisorFormula()
    {
        Formula basis = F.Id("a");
        Formula target = F.Id("b");
        Formula coordinate = F.Id("u");
        Formula ring = Call("ZMod", D(8));
        return Disp(Seq(
            Exists, Sp, basis, Comma, Sp, target, Colon, Sp, ring, Comma, RowBreak, Grp(),
            basis, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            Span(target), Sp, Eq, Sp, Span(basis), Sp, Land, Sp,
            Neg, Sp, Exists, Bang, Sp, coordinate, Colon, Sp, Call("Units", ring), Comma,
            Sp, UnitAction(basis, coordinate), Sp, Eq, Sp, target, Dot));
    }

    private static Formula NonemptyCarrierFormula()
    {
        Formula ring = F.Id("R");
        return Disp(Seq(
            Forall, Sp, ring, Comma, Sp, Call("Zero", ring), Sp, Rightarrow, Sp,
            Call("Nonempty", ring), Dot));
    }
}
