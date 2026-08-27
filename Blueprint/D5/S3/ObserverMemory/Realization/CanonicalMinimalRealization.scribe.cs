using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Realization;

internal sealed class CanonicalMinimalRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula xType = F.Id("X");
        Formula stateType = F.Id("S");
        Formula outputType = F.Id("B");
        Formula x = F.Id("x");
        Formula state = F.Id("s");
        Formula f = F.Id("F");
        Formula q = F.Id("q");
        Formula r = F.Id("R");
        Formula nu = F.Id("nu");
        Formula readout = F.Id("o");
        Formula pi = F.Id("pi");
        Formula hcommute = F.Id("hcommute");
        Formula hreadout = F.Id("hreadout");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula rOfX = new Formula.Apply(r, [x]);
        Formula fOfX = new Formula.Apply(f, [x]);
        Formula rOfFOfX = new Formula.Apply(r, [fOfX]);
        Formula nuOfRofX = new Formula.Apply(nu, [rOfX]);
        Formula qOfX = new Formula.Apply(q, [x]);
        Formula oOfRofX = new Formula.Apply(readout, [rOfX]);
        Formula rangeR = new Formula.Apply(
            Seq(Operatorname, Grp(F.Id("range"))), [r]);
        Formula bq = new Formula.Subscript(F.Id("b"), q);
        Formula zq = new Formula.Subscript(F.Id("Z"), q);
        Formula rangeBq = new Formula.Apply(
            Seq(Operatorname, Grp(F.Id("range"))), [bq]);
        Formula rangeFactorR = new Formula.Apply(
            Seq(Operatorname, Grp(F.Id("rangeFactorization"))), [r]);
        Formula reachableUpdate = new Formula.Apply(
            Seq(Operatorname, Grp(F.Id("reachableUpdate"))), [f, r, nu, hcommute]);
        Formula shift = F.Id("shift");

        Formula invariantStatement = Disp(Seq(
            Forall, Sp, xType, Comma, Sp, stateType, Colon, Sp, type, Comma, RowBreak,
            Grp(), f, Colon, Sp, new Formula.TypeArrow(xType, xType), Comma, Sp,
            r, Colon, Sp, new Formula.TypeArrow(xType, stateType), Comma, Sp,
            nu, Colon, Sp, new Formula.TypeArrow(stateType, stateType), Comma, RowBreak,
            Grp(), Open, Forall, Sp, x, Comma, Sp,
            rOfFOfX, Sp, Eq, Sp, nuOfRofX, Close, Sp, Rightarrow, RowBreak,
            Grp(), Forall, Sp, state, Sp, InMacro, Sp, rangeR, Comma, Sp,
            new Formula.Apply(nu, [new Formula.Apply(
                Seq(Operatorname, Grp(F.Id("val"))), [state])]),
            Sp, InMacro, Sp, rangeR, Dot));

        Formula mainStatement = Disp(Seq(
            Forall, Sp, xType, Comma, Sp, stateType, Comma, Sp, outputType,
            Colon, Sp, type, Comma, RowBreak,
            Grp(), f, Colon, Sp, new Formula.TypeArrow(xType, xType), Comma, Sp,
            q, Colon, Sp, new Formula.TypeArrow(xType, outputType), Comma, Sp,
            r, Colon, Sp, new Formula.TypeArrow(xType, stateType), Comma, RowBreak,
            Grp(), nu, Colon, Sp, new Formula.TypeArrow(stateType, stateType), Comma, Sp,
            readout, Colon, Sp, new Formula.TypeArrow(stateType, outputType), Comma, RowBreak,
            Grp(), hcommute, Colon, Sp, Forall, Sp, x, Colon, Sp, xType, Comma, Sp,
            rOfFOfX, Sp, Eq, Sp, nuOfRofX, Comma, RowBreak,
            Grp(), hreadout, Colon, Sp, Forall, Sp, x, Colon, Sp, xType, Comma, Sp,
            qOfX, Sp, Eq, Sp, oOfRofX, Comma, RowBreak,
            Grp(), bq, Sp, Eq, Sp,
            new Formula.Apply(Seq(Operatorname, Grp(F.Id("completeItinerary"))), [f, q]),
            Comma, Sp, zq, Sp, Eq, Sp, rangeBq, Comma, RowBreak,
            Grp(), Exists, Bang, Sp, pi, Colon, Sp,
            new Formula.TypeArrow(rangeR, zq), Comma, Sp,
            new Formula.Apply(Seq(Operatorname, Grp(F.Id("Surjective"))), [pi]),
            Sp, Land, RowBreak,
            Grp(), bq, Sp, Eq, Sp, pi, Sp, Circ, Sp, rangeFactorR,
            Sp, Land, RowBreak,
            Grp(), pi, Sp, Circ, Sp, reachableUpdate,
            Sp, Eq, Sp, shift, Sp, Circ, Sp, pi, Dot));

        Formula readoutNotExact = new Formula.Not(Seq(
            Forall, Sp, x, Comma, Sp, qOfX, Sp, Eq, Sp, oOfRofX));
        Formula noReadoutFactor = new Formula.Not(Seq(
            Exists, Sp, pi, Colon, Sp, new Formula.TypeArrow(rangeR, zq), Comma, Sp,
            Forall, Sp, x, Comma, Sp,
            new Formula.Apply(pi, [new Formula.Apply(
                Seq(Operatorname, Grp(F.Id("rangeFactorization"))), [r, x])]),
            Sp, Eq, Sp,
            new Formula.Apply(
                Seq(Operatorname, Grp(F.Id("rangeFactorization"))), [bq, x])));
        Formula readoutWitnessStatement = Disp(Seq(
            xType, Sp, Eq, Sp, outputType, Sp, Eq, Sp,
            Seq(Operatorname, Grp(F.Id("Bool"))), Comma, Sp,
            stateType, Sp, Eq, Sp, Seq(Operatorname, Grp(F.Id("Unit"))), Comma, RowBreak,
            Grp(), f, Sp, Eq, Sp, F.Id("id"), Comma, Sp,
            nu, Sp, Eq, Sp, F.Id("id"), Comma, Sp,
            r, Open, x, Close, Sp, Eq, Sp, F.Id("star"), Comma, Sp,
            q, Sp, Eq, Sp, F.Id("id"), Comma, Sp,
            new Formula.Apply(readout, [F.Id("star")]), Sp, Eq, Sp, D(0), RowBreak,
            Rightarrow, Sp,
            Open, Forall, Sp, x, Comma, Sp,
            rOfFOfX, Sp, Eq, Sp, nuOfRofX, Close, Sp, Land, Sp,
            readoutNotExact, Sp, Land, RowBreak,
            Grp(), noReadoutFactor, Dot));

        Formula updatesDoNotCommute = new Formula.Not(Seq(
            Forall, Sp, x, Comma, Sp, rOfFOfX, Sp, Eq, Sp, nuOfRofX));
        Formula rangeIsNotInvariant = new Formula.Not(Seq(
            Forall, Sp, state, Sp, InMacro, Sp, rangeR, Comma, Sp,
            new Formula.Apply(nu, [new Formula.Apply(
                Seq(Operatorname, Grp(F.Id("val"))), [state])]),
            Sp, InMacro, Sp, rangeR));
        Formula updateWitnessStatement = Disp(Seq(
            xType, Sp, Eq, Sp, outputType, Sp, Eq, Sp,
            Seq(Operatorname, Grp(F.Id("Unit"))), Comma, Sp,
            stateType, Sp, Eq, Sp, Seq(Operatorname, Grp(F.Id("Bool"))), Comma, RowBreak,
            Grp(), f, Sp, Eq, Sp, F.Id("id"), Comma, Sp,
            r, Open, x, Close, Sp, Eq, Sp, D(0), Comma, Sp,
            nu, Sp, Eq, Sp, Seq(Operatorname, Grp(F.Id("not"))), Comma, RowBreak,
            Grp(), Open, Forall, Sp, x, Comma, Sp,
            qOfX, Sp, Eq, Sp, oOfRofX, Close, Sp, Land, Sp,
            updatesDoNotCommute, Sp, Land, RowBreak,
            Grp(), rangeIsNotInvariant, Dot));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Exact realizations map canonically onto the realized complete itineraries.",
            H("Canonical Minimal Realization"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("realization-image-is-invariant-under-realized-update"),
                    DeclarationHandle.Create(
                        "D5/S3/ObserverMemory/Realization/CanonicalMinimalRealization."
                            + "realization_range_invariant"),
                    H("The realization image is update invariant"),
                    StatementSource.FromAuthor(invariantStatement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let R intertwine a source update F with a realized update nu. "
                                + "Every point of range(R) has the form R(x), and applying nu "
                                + "produces R(F(x)), which lies in the same range.")),
                        Paragraph(Text(
                            "This closure result defines the reachable update used by the main "
                                + "minimal-realization theorem. No global surjectivity of R onto "
                                + "its ambient carrier is assumed."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("exact-realizations-factor-onto-causal-itineraries"),
                    DeclarationHandle.Create(
                        "D5/S3/ObserverMemory/Realization/CanonicalMinimalRealization."
                            + "canonical_minimal_realization"),
                    H("Exact realizations factor onto causal itineraries"),
                    StatementSource.FromAuthor(mainStatement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For a source update F and readout q, bq is the complete infinite "
                                + "itinerary and Zq is its realized range. An exact realization "
                                + "R commutes with update and factors the current readout through "
                                + "a realized readout o.")),
                        Paragraph(Text(
                            "There is a unique surjection pi from range(R) onto Zq. It sends "
                                + "R(x) to bq(x), so the displayed factorization is independent "
                                + "of the chosen source representative.")),
                        Paragraph(Text(
                            "The reachable update is induced by nu using the preceding range "
                                + "invariance theorem. The existing itinerary update is literal "
                                + "left shift, and pi intertwines these two updates.")),
                        Paragraph(Text(
                            "The proof reuses the repository's complete-itinerary universality "
                                + "and causal-state image factorization theorems. Pinned Mathlib "
                                + "supplies surjective range factorization and cancellation for "
                                + "the uniqueness step."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("exact-readout-condition-has-a-finite-witness"),
                    DeclarationHandle.Create(
                        "D5/S3/ObserverMemory/Realization/CanonicalMinimalRealization."
                            + "readout_exactness_is_necessary"),
                    H("Exact readout factorization has a finite witness"),
                    StatementSource.FromAuthor(readoutWitnessStatement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Take Boolean source and output carriers, a one-point realization "
                                + "carrier, identity dynamics, and Boolean identity readout. The "
                                + "realization collapses false and true while their constant "
                                + "future itineraries remain distinct.")),
                        Paragraph(Text(
                            "Thus update commutation still holds, but the proposed realized "
                                + "readout is not exact and no map on range(R) can agree with both "
                                + "source itineraries. This finite witness prevents deletion of "
                                + "the readout-factorization hypothesis."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("update-commutation-condition-has-a-finite-witness"),
                    DeclarationHandle.Create(
                        "D5/S3/ObserverMemory/Realization/CanonicalMinimalRealization."
                            + "update_commutation_is_necessary"),
                    H("Update commutation has a finite witness"),
                    StatementSource.FromAuthor(updateWitnessStatement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Take a one-point source with exact one-point readout, embed it as "
                                + "false in a Boolean realization carrier, and let the proposed "
                                + "realized update be Boolean negation.")),
                        Paragraph(Text(
                            "The readout condition holds, but negation sends the only reachable "
                                + "realization state outside range(R). Hence the realized update "
                                + "does not induce an update on the reachable part, witnessing "
                                + "the need for update commutation."))),
                    DescribeRole.Theorem))));
    }
}
