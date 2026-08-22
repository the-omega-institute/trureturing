using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class ReducedRecordAccessDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reversible record coupling can preserve coherence globally while making it inaccessible to every reduced-state decoder.",
        H("Reduced Record Access Defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reversible-record-coupling-exposes-a-reduced-access-defect"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Decoherence/ReducedRecordAccessDefect."
                        + "reduced_irreversibility_is_access_defect"),
                H("Reduced irreversibility is an access defect"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let rho and sigma be system matrices with the same populations and a "
                            + "different off-diagonal coherence. The environment begins in its "
                            + "blank address state, and a controlled-copy permutation writes the "
                            + "system address into the canonical environment-record state.")),
                    Paragraph(Text(
                        "The permutation matrix is unitary and sends both blank-record inputs to "
                            + "their respective joint record states. Those joint states remain "
                            + "distinct, but tracing the environment makes the two reduced system "
                            + "states equal, so no function of that reduced state can reconstruct "
                            + "both phase-bearing joint records.")),
                    Paragraph(Text(
                        "Applying the adjoint global coupling to either joint record restores its "
                            + "original blank-record input exactly. Thus the loss is caused by "
                            + "excluding the record degrees of freedom from the available control "
                            + "domain, not by irreversibility of the global evolution."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
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

    private static Formula Entry(Formula matrix, Formula i, Formula j) =>
        Seq(matrix, Underscore, Grp(i, j));

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula rho = Rho;
        Formula sigma = SigmaLower;
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula unitary = F.Id("U");
        Formula matrixType = Seq(Operatorname, Grp(F.Id("QubitMatrix")));
        Formula jointType = Seq(Operatorname, Grp(F.Id("JointQubitEnvironmentMatrix")));
        Formula recordRho = Apply("record", rho);
        Formula recordSigma = Apply("record", sigma);
        Formula blankRho = Apply("blank", rho);
        Formula blankSigma = Apply("blank", sigma);
        Formula traceRho = Apply("traceEnvironment", recordRho);
        Formula traceSigma = Apply("traceEnvironment", recordSigma);
        Formula forwardRho = Apply("evolve", unitary, blankRho);
        Formula forwardSigma = Apply("evolve", unitary, blankSigma);
        Formula adjoint = Seq(unitary, Caret, Grp(Star));
        Formula reverseRho = Apply("evolve", adjoint, recordRho);
        Formula reverseSigma = Apply("evolve", adjoint, recordSigma);
        Formula recover = F.Id("recover");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, rho, Comma, Sp, sigma, Colon, Sp, matrixType, Comma, RowBreak, Grp(),
            Open, Forall, Sp, i, Comma, Sp, Entry(rho, i, i), Sp, Eq, Sp,
                Entry(sigma, i, i), Close, Sp, Land, RowBreak, Grp(),
            Open, Exists, Sp, i, Comma, Sp, j, Comma, Sp, i, Sp, Neq, Sp, j,
                Sp, Land, Sp, Entry(rho, i, j), Sp, Neq, Sp, Entry(sigma, i, j), Close,
                Sp, Rightarrow, RowBreak, Grp(),
            Apply("Unitary", unitary), Sp, Land, RowBreak, Grp(),
            forwardRho, Sp, Eq, Sp, recordRho, Sp, Land, RowBreak, Grp(),
            forwardSigma, Sp, Eq, Sp, recordSigma, Sp, Land, RowBreak, Grp(),
            traceRho, Sp, Eq, Sp, traceSigma, Sp, Land, RowBreak, Grp(),
            recordRho, Sp, Neq, Sp, recordSigma, Sp, Land, RowBreak, Grp(),
            Open, Neg, Exists, Sp, recover, Colon, Sp,
                new Formula.TypeArrow(matrixType, jointType), Comma, RowBreak, Grp(),
            Open, At(recover, traceRho), Sp, Eq, Sp, recordRho, Sp, Land, RowBreak, Grp(),
                At(recover, traceSigma), Sp, Eq, Sp, recordSigma, Close, Close,
                Sp, Land, RowBreak, Grp(),
            reverseRho, Sp, Eq, Sp, blankRho, Sp, Land, RowBreak, Grp(),
            reverseSigma, Sp, Eq, Sp, blankSigma, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
