using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Naturality;

internal sealed class DiagonalNaturalityDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The worst diagonal naturality defect is exactly the semiconjugacy defect.",
        H("Diagonal Naturality Defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("diagonal-naturality-defect-equals-semiconjugacy-defect"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Naturality/DiagonalNaturalityDefect."
                        + "diagonal_naturality_defect_eq_semiconjugacy_defect"),
                H("Diagonal naturality defect equals semiconjugacy defect"),
                StatementSource.FromAuthor(DiagonalDefectFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let A be a nonempty address type, Y a finite state type, and Z an "
                            + "observed space. Let tau and sigma update Y and Z, and let pi "
                            + "project Y to Z. Apply pi pointwise to tables and output vectors, "
                            + "and read a table diagonally before applying its update.")),
                    Paragraph(Text(
                        "For every table E and address a, the observed distance between "
                            + "projecting after the Y-update and applying the Z-update after "
                            + "projection is bounded by the uniform semiconjugacy defect. The "
                            + "supremum over all tables and addresses is exactly that defect.")),
                    Paragraph(Text(
                        "The upper bound applies the imported semiconjugacy-defect definition "
                            + "pointwise. For the reverse bound, each state y is placed in a "
                            + "constant table and evaluated at an address supplied by nonemptiness. "
                            + "Loogle supplied the exact le_iSup and iSup_le declarations used "
                            + "for both supremum directions. LeanSearch returned HTTP 404 for "
                            + "the full query, and pinned-library and repository searches found "
                            + "no complete theorem with this statement."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Apply(Formula function, Formula first, Formula second) =>
        Seq(function, Open, first, Comma, Sp, second, Close);

    private static Formula DiagonalDefectFormula()
    {
        Formula addressType = F.Id("A");
        Formula stateType = F.Id("Y");
        Formula table = F.Id("E");
        Formula address = F.Id("a");
        Formula pPi = Seq(F.Id("P"), Underscore, Grp(Pi));
        Formula qPi = Seq(F.Id("Q"), Underscore, Grp(Pi));
        Formula deltaTau = Seq(Delta, Underscore, Grp(Tau));
        Formula deltaSigma = Seq(Delta, Underscore, Grp(SigmaLower));
        Formula distance = Seq(F.Id("d"), Underscore, Grp(F.Id("Z")));
        Formula defect = Seq(
            DeltaLower, Open, Pi, Semi, Sp, Tau, Comma, Sp, SigmaLower, Close);
        Formula defectAt = Apply(
            distance,
            Apply(Apply(qPi, Apply(deltaTau, table)), address),
            Apply(Apply(deltaSigma, Apply(pPi, table)), address));
        Formula tableType = new Formula.TypeArrow(
            Seq(addressType, Sp, Times, Sp, addressType), stateType);
        Formula pointwise = Seq(
            Forall, Sp, table, Colon, Sp, tableType, Comma, Sp,
            Forall, Sp, address, Sp, InMacro, Sp, addressType, Comma, Esc,
            defectAt, Sp, Leq, Sp, defect);
        Formula exactSupremum = Seq(
            Operatorname, Grp(F.Id("sup")), Underscore, Grp(table), Sp,
            Operatorname, Grp(F.Id("sup")), Underscore, Grp(address, Sp, InMacro, Sp, addressType), Sp,
            defectAt, Sp, Eq, Sp, defect);

        return Disp(Seq(Open, pointwise, Close, Sp, Land, Esc, exactSupremum, Dot));
    }
}
