using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeHierarchy;

internal sealed class StructuralCatalogDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Structural strictness is certified by relation inclusion and a separating pair, and finite embeddings preserve the verdict.",
        H("Structural Catalog Strictness"),
        Blocks(
            DefinitionNode("structural-joint-kernel", "jointKernel", "Structural joint kernel",
                "Two states are related exactly when every primitive of every selected theorem relates them."),
            DefinitionNode("structurally-lowers-escape", "StructurallyLowersEscape",
                "Structural escape lowering",
                "The full relation refines the leave-one-out relation and the reverse pointwise refinement fails."),
            DefinitionNode("structural-strictness-certificate",
                "StructuralStrictnessCertificate", "Structural strictness certificate",
                "A certificate stores full-to-without inclusion and a pair accepted without the theorem but rejected by the full catalog."),
            TheoremNode("certificate-implies-structural-strictness",
                "structurallyLowersEscape_of_certificate",
                "A certificate proves structural strictness", CertificateForwardFormula(),
                "Applying a hypothetical reverse inclusion to the certificate pair contradicts full separation."),
            TheoremNode("structural-strictness-yields-certificate",
                "exists_certificate_of_structurallyLowersEscape",
                "Structural strictness yields a certificate", CertificateReverseFormula(),
                "Classical failure of reverse pointwise inclusion supplies the separating pair."),
            TheoremNode("structural-strictness-certificate-equivalence",
                "structurallyLowersEscape_iff_exists_certificate",
                "Structural strictness is certificate inhabitation", CertificateIffFormula(),
                "The strictness proposition and the inhabited certificate type determine one another."),
            TheoremNode("finite-triviality-is-not-lowering",
                "trivialInCatalog_iff_not_lowersEscape",
                "Finite triviality is failure to lower escape", FiniteTrivialFormula(),
                "On a nondegenerate finite arena, the landed positive-count criterion turns empty unique capture into the negated rate verdict."),
            TheoremNode("set-selection-kernel-embedding",
                "toStructuralCatalog_jointKernel_relation_iff_set",
                "Set selection kernels are preserved", SetJointKernelBridgeFormula(),
                "For every Set-indexed selection, the embedded structural relation " +
                "is exactly the landed joint kernel relation."),
            TheoremNode("finite-selection-kernel-embedding",
                "toStructuralCatalog_jointKernel_relation_iff",
                "Finite selection kernels are preserved", JointKernelBridgeFormula(),
                "For every finite selection, the embedded structural relation is the landed indistinguishability relation."),
            DefinitionNode("finite-witness-to-structural-certificate",
                "toStructuralCatalog_certificate_of_uniqueCapture_witness",
                "Finite witness to structural certificate",
                "A finite unique-capture pair constructs a structural certificate with exactly the same left and right states."),
            TheoremNode("structural-certificate-to-finite-witness",
                "uniqueCapture_witness_of_toStructuralCatalog_certificate",
                "Structural certificate to finite witness", WitnessReverseFormula(),
                "An embedded certificate preserves its pair and yields distinctness, leave-one-out agreement, and separation by the removed theorem."),
            TheoremNode("structural-certificate-positive-capture-equivalence",
                "toStructuralCatalog_exists_certificate_iff_uniqueCaptureCount_pos",
                "Structural certificates are positive finite capture", CertificateCountFormula(),
                "The landed finite witness theorem transports the same separating pair in both directions."),
            TheoremNode("finite-structural-verdict-embedding",
                "toStructuralCatalog_structurallyLowersEscape_iff",
                "Finite structural verdicts are preserved", StructuralBridgeFormula(),
                "The universal pointwise-order verdict agrees with the landed finite Set-level verdict."),
            TheoremNode("finite-rate-verdict-embedding",
                "toStructuralCatalog_structurallyLowersEscape_iff_lowersEscape",
                "Finite rate verdicts are preserved", RateBridgeFormula(),
                "On a nondegenerate arena, the structural embedding agrees with the exact finite escape-rate verdict."))));

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

    private static Formula IffFormula(Formula left, Formula right) =>
        Seq(left, Sp, Leftrightarrow, Sp, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Lowers() =>
        Call("StructurallyLowersEscape", F.Id("catalog"), F.Id("i"));

    private static Formula Certificate() =>
        Call("StructuralStrictnessCertificate", F.Id("catalog"), F.Id("i"));

    private static Formula CertificateForwardFormula() => Disp(Seq(
        Forall, Sp, F.Id("certificate"), Colon, Sp, Certificate(), Comma, Sp,
        Lowers(), Dot));

    private static Formula CertificateReverseFormula() => Disp(Seq(
        ImpliesFormula(
            Lowers(),
            Call("Nonempty", Certificate())), Dot));

    private static Formula CertificateIffFormula() => Disp(Seq(
        IffFormula(Lowers(), Call("Nonempty", Certificate())), Dot));

    private static Formula FiniteTrivialFormula() => Disp(Seq(
            ImpliesFormula(
                Call("Nondegenerate", F.Id("arena")),
            Grp(IffFormula(
                Call("TrivialInCatalog", F.Id("catalog"), F.Id("i")),
                Seq(Neg, Call("LowersEscape", F.Id("catalog"), F.Id("i")))))), Dot));

    private static Formula SetJointKernelBridgeFormula()
    {
        Formula selected = F.Id("S");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula pair = Seq(Open, left, Comma, Sp, right, Close);
        Formula selectedType = Call("Set", Call("Index", F.Id("catalog")));
        return Disp(Seq(
            Forall, Sp, selected, Colon, Sp, selectedType, Comma, Sp,
            left, Comma, Sp, right, Comma, Sp,
            IffFormula(
                Call("relation",
                    Call("jointKernel", Call("toStructuralCatalog", F.Id("catalog")),
                        selected), left, right),
                new Formula.Relation(
                    pair,
                    FormulaRelationOperator.MemberOf,
                    Call("jointKernel", F.Id("catalog"), selected))),
            Dot));
    }

    private static Formula JointKernelBridgeFormula() => Disp(Seq(
        Forall, Sp, F.Id("S"), Comma, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
        IffFormula(
            Call("relation",
                Call("jointKernel", Call("toStructuralCatalog", F.Id("catalog")),
                    Call("coe", F.Id("S"))), F.Id("x"), F.Id("y")),
            Call("indistinguishable", F.Id("catalog"), F.Id("S"), F.Id("x"), F.Id("y"))),
        Dot));

    private static Formula WitnessReverseFormula()
    {
        Formula certificate = F.Id("certificate");
        Formula left = Call("left", certificate);
        Formula right = Call("right", certificate);
        Formula distinct = Seq(left, Sp, Neq, Sp, right);
        Formula withoutAgreement = Seq(
            Forall, Sp, F.Id("j"), Comma, Sp,
            ImpliesFormula(
                Seq(F.Id("j"), Sp, Neq, Sp, F.Id("i")),
                Call("agrees", F.Id("catalog"), F.Id("j"), left, right)));
        Formula separation = Seq(Neg,
            Call("agrees", F.Id("catalog"), F.Id("i"), left, right));
        return Disp(Seq(
            Forall, Sp, certificate, Colon, Sp,
            Call("StructuralStrictnessCertificate",
                Call("toStructuralCatalog", F.Id("catalog")), F.Id("i")), Comma, Sp,
            new Formula.Logic(
                distinct,
                FormulaLogicOperator.And,
                new Formula.Logic(
                    Grp(withoutAgreement),
                    FormulaLogicOperator.And,
                    separation)), Dot));
    }

    private static Formula CertificateCountFormula() => Disp(Seq(
        IffFormula(
            Call("Nonempty",
                Call("StructuralStrictnessCertificate",
                    Call("toStructuralCatalog", F.Id("catalog")), F.Id("i"))),
            new Formula.Relation(
                D(0),
                FormulaRelationOperator.LessThan,
                Call("uniqueCaptureCount", F.Id("catalog"), F.Id("i")))), Dot));

    private static Formula StructuralBridgeFormula() => Disp(Seq(
        IffFormula(
            Call("StructurallyLowersEscape",
                Call("toStructuralCatalog", F.Id("catalog")), F.Id("i")),
            Call("StructurallyLowersEscape", F.Id("catalog"), F.Id("i"))), Dot));

    private static Formula RateBridgeFormula() => Disp(Seq(
        ImpliesFormula(
            Call("Nondegenerate", F.Id("arena")),
            Grp(IffFormula(
                Call("StructurallyLowersEscape",
                    Call("toStructuralCatalog", F.Id("catalog")), F.Id("i")),
                Call("LowersEscape", F.Id("catalog"), F.Id("i"))))), Dot));
}
