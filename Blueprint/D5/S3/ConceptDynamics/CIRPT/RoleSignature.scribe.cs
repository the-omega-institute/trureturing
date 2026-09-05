using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CIRPT;

internal sealed class RoleSignatureDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/CIRPT/RoleSignature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four Boolean role coordinates classify every finite off-diagonal state pair.",
        H("CIRPT Four-Role Signatures"),
        Blocks(
            DefinitionNode("axis-ordinal", "axisOrdinal", "Role coordinate",
                "Each CIRPT primitive role receives its canonical coordinate in Fin 4."),
            DefinitionNode("axis-of-ordinal", "axisOfOrdinal", "Coordinate decoder",
                "A four-bit coordinate decodes to its corresponding primitive role."),
            DefinitionNode("axis-separation", "separatesOnAxis", "Axis separation",
                "Axis separation detects whether a matching atom rejects the supplied pair."),
            DefinitionNode("role-signature", "roleSignature", "Role signature",
                "The role signature records axis separation at each of the four coordinates."),
            DefinitionNode("off-diagonal-pairs", "offDiagonalPairs",
                "Ordered off-diagonal pairs",
                "The generic finite carrier contains all ordered pairs with distinct entries."),
            DefinitionNode("axis-separation-pairs", "separationPairsOnAxis",
                "Axis separation pairs",
                "This finset filters off-diagonal pairs by separation on one role axis."),
            DefinitionNode("signature-histogram", "signatureHistogram",
                "Signature histogram",
                "The CIRPT-38 raw histogram counts ordered off-diagonal pairs with each exact bundle signature."),
            DefinitionNode("residual-role-signature", "residualRoleSignature",
                "Residual role signature",
                "The CIRPT-16 defect signature qualifies every role-separation bit by the current kernel."),
            DefinitionNode("role-defect-pairs", "roleDefectPairs",
                "Finite role-defect pairs",
                "This finset restricts a named bundle role defect to ordered off-diagonal pairs."),
            DefinitionNode("residual-signature-histogram", "residualSignatureHistogram",
                "Residual signature histogram",
                "The current-qualified histogram counts each CIRPT-IE-011 defect signature."),
            TheoremNode("coordinate-decoding", "axisOfOrdinal_axisOrdinal",
                "Coordinate decoding returns the role", CoordinateFormula(),
                "Encoding and then decoding any primitive role returns that role."),
            TheoremNode("axis-separation-reflection", "separatesOnAxis_eq_true_iff",
                "Axis separation reflects an atom witness", SeparationFormula(),
                "The Boolean axis test is true exactly when a matching atom rejects the pair."),
            TheoremNode("agreement-is-zero-signature", "agrees_iff_roleSignature_zero",
                "Agreement is the zero signature", AgreementFormula(),
                "A bundle relates a pair exactly when none of its four roles separates it."),
            TheoremNode("bundle-signature-partition", "bundle_signature_partition",
                "Raw bundle signatures partition off-diagonal pairs", BundlePartitionFormula(),
                "CIRPT-38 partitions the complete off-diagonal carrier by raw bundle signature."),
            TheoremNode("bundle-signature-histogram-axis-count", "bundle_signature_histogram_axis_count",
                "Raw bundle histogram role counts are exact", BundleAxisCountFormula(),
                "Summing raw CIRPT-38 classes with one role bit set recovers that axis separation count."),
            TheoremNode("four-role-signature-partition", "four_role_signature_partition",
                "Current-qualified four-role signatures partition pairs", ResidualPartitionFormula(),
                "CIRPT-16 / CIRPT-IE-011 partitions all off-diagonal pairs by current-qualified defect signature."),
            TheoremNode("residual-signature-role-count", "residual_signature_histogram_role_count",
                "Residual histogram role counts are exact", ResidualAxisCountFormula(),
                "CIRPT-IE-011 recovers the exact finite cardinality of every named role defect."),
            TheoremNode("residual-is-nonzero-signature",
                "mem_kernelResidual_iff_residualRoleSignature_ne_zero",
                "Residual membership is a nonzero defect signature", ResidualNonzeroFormula(),
                "CIRPT-16 identifies residual membership with a nonzero current-qualified signature."))));

    private static DocumentBlock.Describe DefinitionNode(
        string id, string declaration, string title, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe TheoremNode(
        string id, string declaration, string title, Formula formula, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula CoordinateFormula() => Disp(Seq(
        Forall, Sp, F.Id("axis"), Comma, Sp,
        Call("axisOfOrdinal", Call("axisOrdinal", F.Id("axis"))),
        Sp, Eq, Sp, F.Id("axis"), Dot));

    private static Formula SeparationFormula()
    {
        Formula atom = Call("atom", F.Id("b"), F.Id("i"));
        Formula witness = Seq(
            Call("axis", atom), Sp, Eq, Sp, F.Id("role"),
            Sp, Land, Sp, Neg,
            Call("relation", Call("kernel", atom), F.Id("x"), F.Id("y")));
        return Disp(Seq(
            Call("separatesOnAxis", F.Id("b"), F.Id("role"), F.Id("x"), F.Id("y")),
            Sp, Eq, Sp, F.Id("true"), Sp, Iff, Sp,
            Exists, Sp, F.Id("i"), Comma, Sp, witness, Dot));
    }

    private static Formula AgreementFormula()
    {
        Formula zero = Seq(LambdaLower, Sp, F.Id("coordinate"), Comma, Sp, F.Id("false"));
        return Disp(Seq(
            Call("agrees", F.Id("b"), F.Id("x"), F.Id("y")), Sp, Iff, Sp,
            Call("roleSignature", F.Id("b"), F.Id("x"), F.Id("y")),
            Sp, Eq, Sp, zero, Dot));
    }

    private static Formula BundlePartitionFormula()
    {
        Formula summand = Call("signatureHistogram", F.Id("b"), F.Id("s"));
        return Disp(Seq(
            Sum, Underscore, Grp(F.Id("s")), Sp, summand,
            Sp, Eq, Sp, Call("card", Call("offDiagonalPairs", F.Id("X"))), Dot));
    }

    private static Formula BundleAxisCountFormula()
    {
        Formula condition = Seq(
            Call("s", Call("axisOrdinal", F.Id("axis"))), Sp, Eq, Sp, F.Id("true"));
        Formula summand = Call("signatureHistogram", F.Id("b"), F.Id("s"));
        return Disp(Seq(
            Sum, Underscore, Grp(F.Id("s"), Colon, Sp, condition), Sp, summand,
            Sp, Eq, Sp,
            Call("card", Call("separationPairsOnAxis", F.Id("b"), F.Id("axis"))), Dot));
    }

    private static Formula ResidualPartitionFormula() => Disp(Seq(
        Sum, Underscore, Grp(F.Id("s")), Sp,
        Call("residualSignatureHistogram", F.Id("K"), F.Id("b"), F.Id("s")),
        Sp, Eq, Sp, Call("card", Call("offDiagonalPairs", F.Id("X"))), Dot));

    private static Formula ResidualAxisCountFormula()
    {
        Formula condition = Seq(Call("s", F.Id("r")), Sp, Eq, Sp, F.Id("true"));
        return Disp(Seq(
            Sum, Underscore, Grp(F.Id("s"), Colon, Sp, condition), Sp,
            Call("residualSignatureHistogram", F.Id("K"), F.Id("b"), F.Id("s")),
            Sp, Eq, Sp,
            Call("card", Call("roleDefectPairs", F.Id("K"), F.Id("b"),
                Call("axisOfOrdinal", F.Id("r")))), Dot));
    }

    private static Formula ResidualNonzeroFormula() => Disp(Seq(
        F.Id("p"), Sp, InMacro, Sp,
        Call("kernelResidual", F.Id("K"), Call("toKernel", F.Id("b"))),
        Sp, Iff, Sp,
        NotEqual(
            Call("residualRoleSignature", F.Id("K"), F.Id("b"), F.Id("p")),
            F.Id("zero")), Dot));
}
