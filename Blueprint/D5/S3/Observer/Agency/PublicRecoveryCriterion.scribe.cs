using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Agency;

internal sealed class PublicRecoveryCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Agency/PublicRecoveryCriterion.public_recovery_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Public recovery through an additive observation is equivalent to kernel "
            + "containment and to vanishing covert transport; adding a ledger can only "
            + "shrink the covert image.",
        H("Public Recovery Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("public-recovery-kernel-and-throat-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Public recovery, kernel containment, and ledger refinement"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The control, public, hidden, and ledger carriers are additive groups. "
                        + "The public observation H, hidden transport K, and ledger L are "
                        + "additive homomorphisms, matching the source's uses of kernels, "
                        + "zero, intersection, and kernel image.")),
                Paragraph(Text(
                    "A recovery homomorphism on the realized public image exists exactly "
                        + "when every publicly silent control is also hidden-silent. The "
                        + "covert throat is represented by the additive image K(ker H), so "
                        + "its vanishing is the same kernel condition.")),
                Paragraph(Text(
                    "Adding the ledger replaces ker H by ker H intersect ker L. This is a "
                        + "subgroup of ker H, and monotonicity of additive image proves that "
                        + "the remaining covert transport can only shrink."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula TheoremFormula()
    {
        Formula control = F.Id("U");
        Formula publicCarrier = F.Id("P");
        Formula hidden = Seq(Mathcal, Grp(F.Id("K")));
        Formula ledger = Lambda;
        Formula observation = F.Id("H");
        Formula transport = F.Id("K");
        Formula ledgerMap = F.Id("L");
        Formula recoveryMap = Seq(Overline, Grp(transport));

        Formula kernelH = Call("ker", observation);
        Formula kernelK = Call("ker", transport);
        Formula kernelL = Call("ker", ledgerMap);
        Formula recovery = Seq(
            Exists, Sp, recoveryMap, Colon, Sp,
            Call("AddMonoidHom", Call("im", observation), hidden), Comma, Sp,
            transport, Sp, Eq, Sp,
            recoveryMap, Sp, Circ, Sp, observation);
        Formula kernelInclusion = Seq(
            kernelH, Sp, Subseteq, Sp, kernelK);
        Formula covertThroat = Call("image", transport, kernelH);
        Formula throatZero = Seq(covertThroat, Sp, Eq, Sp, D(0));
        Formula ledgerKernel = Call("intersection", kernelH, kernelL);
        Formula ledgerMonotonicity = Seq(
            Call("image", transport, ledgerKernel), Sp, Subseteq, Sp,
            covertThroat);

        Formula equivalences = And(
            IffFormula(recovery, kernelInclusion),
            And(
                IffFormula(kernelInclusion, throatZero),
                IffFormula(throatZero, recovery)));
        Formula conclusion = And(equivalences, ledgerMonotonicity);

        Formula hypotheses = Seq(
            Call("AddGroup", control), Sp, Land, Sp,
            Call("AddGroup", publicCarrier), Sp, Land, Sp,
            Call("AddGroup", hidden), Sp, Land, Sp,
            Call("AddGroup", ledger), Sp, Land, RowBreak, Grp(),
            observation, Colon, Sp,
            Call("AddMonoidHom", control, publicCarrier), Sp, Land, Sp,
            transport, Colon, Sp,
            Call("AddMonoidHom", control, hidden), Sp, Land, Sp,
            ledgerMap, Colon, Sp,
            Call("AddMonoidHom", control, ledger));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, control, Comma, Sp, publicCarrier, Comma, Sp,
            hidden, Comma, Sp, ledger, Colon, Sp, F.Id("Type"), Comma,
            RowBreak, Grp(),
            hypotheses, Sp, Rightarrow, RowBreak, Grp(),
            conclusion, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
