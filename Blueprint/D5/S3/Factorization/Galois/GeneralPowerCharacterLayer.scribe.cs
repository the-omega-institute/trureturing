using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class GeneralPowerCharacterLayerDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite abelian power characters detect exactly the quotient by nth powers.",
        H("General Power Character Layer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complex-nth-roots-of-unity"),
                DeclarationHandle.Create(Prefix + "complexNthRootsOfUnity"),
                H("The complex nth roots of unity"),
                StatementSource.FromAuthor(RootsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The named target is Mathlib's subgroup of complex units whose nth "
                        + "power is one. At n zero this is the full complex unit group."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("power-character"),
                DeclarationHandle.Create(Prefix + "PowerCharacter"),
                H("Characters of order dividing n"),
                StatementSource.FromAuthor(CharacterFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A power character is a group homomorphism into the named complex "
                        + "nth-root target; no surjectivity condition is imposed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("power-subgroup"),
                DeclarationHandle.Create(Prefix + "powerSubgroup"),
                H("The subgroup of nth powers"),
                StatementSource.FromAuthor(PowerSubgroupFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Commutativity makes the nth-power operation a homomorphism. Its "
                        + "range is the named subgroup denoted by G to the nth power."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("power-character-joint-kernel"),
                DeclarationHandle.Create(Prefix + "powerCharacterJointKernel"),
                H("The common kernel of all power characters"),
                StatementSource.FromAuthor(JointKernelDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The joint blind subgroup is the indexed intersection of the kernels "
                        + "of every homomorphism from G to the complex nth roots."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "power-character-joint-kernel-equals-power-subgroup"),
                DeclarationHandle.Create(
                    Prefix + "power_character_joint_kernel_eq_power_subgroup"),
                H("Power characters detect exactly the quotient by nth powers"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every power character kills every nth power. Conversely, Mathlib's "
                            + "finite-abelian duality separates a point from the power "
                            + "subgroup by a complex-unit character.")),
                    Paragraph(Text(
                        "A character trivial on nth powers has image in the complex nth "
                            + "roots, so it belongs to the indexed family and closes the "
                            + "reverse inclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("power-quotient-has-exponent-dividing"),
                DeclarationHandle.Create(
                    Prefix + "power_quotient_has_exponent_dividing"),
                H("The quotient by nth powers has exponent dividing n"),
                StatementSource.FromAuthor(ExponentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every quotient class has nth power one because the nth power of each "
                        + "representative lies in the power subgroup."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("power-subgroup-is-the-maximal-quotient-kernel"),
                DeclarationHandle.Create(
                    Prefix + "power_subgroup_le_iff_quotient_pow_eq_one"),
                H("The power quotient is maximal among exponent-n quotients"),
                StatementSource.FromAuthor(MaximalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A subgroup contains every nth power exactly when every class of its "
                        + "quotient has nth power one. This is the universal maximality "
                        + "asserted for the quotient seen by the character family."))),
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

    private static Formula Mu(Formula index) =>
        new Formula.Subscript(F.Id("mu"), index);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula CharacterType(Formula group, Formula exponent) =>
        Seq(group, Sp, To, Sp, Mu(exponent));

    private static Formula Quotient(Formula group, Formula subgroup) =>
        Call(F.Id("Quotient"), group, subgroup);

    private static Formula RootsFormula()
    {
        Formula n = F.Id("n");
        Formula z = F.Id("z");
        Formula complexUnits = Seq(
            Mathbb, Grp(F.Id("C")), Caret, Grp(Times));
        Formula roots = Seq(
            OpenBrace, z, Sp, InMacro, Sp, complexUnits, Sp, Mid, Sp,
            Power(z, n), Sp, Eq, Sp, D(1), CloseBrace);
        return Disp(Seq(Mu(n), Sp, Eq, Sp, roots, Dot));
    }

    private static Formula CharacterFormula()
    {
        Formula group = F.Id("G");
        Formula n = F.Id("n");
        return Disp(Seq(
            Call(F.Id("PowerCharacter"), group, n), Sp, Eq, Sp,
            CharacterType(group, n), Dot));
    }

    private static Formula PowerSubgroupFormula()
    {
        Formula group = F.Id("G");
        Formula n = F.Id("n");
        Formula powerMap = Seq(F.Id("g"), Sp, Mapsto, Sp, Power(F.Id("g"), n));
        return Disp(Seq(
            Power(group, n), Sp, Eq, Sp, Call(F.Id("range"), powerMap), Dot));
    }

    private static Formula JointKernelDefinitionFormula()
    {
        Formula group = F.Id("G");
        Formula n = F.Id("n");
        Formula character = F.Id("chi");
        Formula index = Seq(character, Colon, Sp, CharacterType(group, n));
        Formula intersection = Seq(
            Operatorname, Grp(F.Id("intersection")), Underscore, Grp(index), Sp,
            Call(F.Id("ker"), character));
        return Disp(Seq(
            Call(F.Id("JointKernel"), group, n), Sp, Eq, Sp, intersection, Dot));
    }

    private static Formula MainFormula()
    {
        Formula group = F.Id("G");
        Formula n = F.Id("n");
        return Disp(Seq(
            Call(F.Id("JointKernel"), group, n), Sp, Eq, Sp, Power(group, n), Dot));
    }

    private static Formula ExponentFormula()
    {
        Formula group = F.Id("G");
        Formula n = F.Id("n");
        Formula quotient = Quotient(group, Power(group, n));
        return Disp(Seq(
            Call(F.Id("exponent"), quotient), Sp, Mid, Sp, n, Dot));
    }

    private static Formula MaximalFormula()
    {
        Formula group = F.Id("G");
        Formula n = F.Id("n");
        Formula subgroup = F.Id("H");
        Formula q = F.Id("q");
        Formula quotient = Quotient(group, subgroup);
        return Disp(Seq(
            Power(group, n), Sp, Leq, Sp, subgroup, Sp, Iff, RowBreak, Grp(),
            Forall, Sp, q, Sp, InMacro, Sp, quotient, Comma, Sp,
            Power(q, n), Sp, Eq, Sp, D(1), Dot));
    }
}
