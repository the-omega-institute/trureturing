using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class AllFutureStatisticsSufficiencyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula Call(string name, params Formula[] arguments)
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

        Formula d = F.Id("d");
        Formula r = F.Id("r");
        Formula time = F.Id("k");
        Formula effectIndex = F.Id("a");
        Formula heisenberg = F.Id("H");
        Formula effects = F.Id("E");
        Formula rho = Rho;
        Formula sigma = SigmaLower;
        Formula carrier = Seq(
            Operatorname, Grp(F.Id("Herm")), Underscore, Grp(d), Caret, Grp(D(0)));
        Formula effect = Seq(effects, Underscore, effectIndex);
        Formula iteratedEffect = Seq(
            heisenberg, Caret, Grp(time), Open, effect, Close);
        Formula rhoExpectation = Seq(
            Langle, rho, Comma, Sp, iteratedEffect, Rangle);
        Formula sigmaExpectation = Seq(
            Langle, sigma, Comma, Sp, iteratedEffect, Rangle);
        Formula rhoProjection = Call("predictiveProjection", heisenberg, effects, rho);
        Formula sigmaProjection = Call("predictiveProjection", heisenberg, effects, sigma);
        Formula statement = Disp(Seq(
            Forall, Sp, d, Comma, Sp, r, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Forall, Sp, heisenberg, Colon, Sp, Call("End", carrier), Comma, Sp,
            Forall, Sp, effects, Colon, Sp,
            Call("Fin", Seq(r, Sp, Plus, Sp, D(1))), Sp, To, Sp, carrier, Comma, Sp,
            Forall, Sp, rho, Comma, Sp, sigma, InMacro, Sp, carrier, Comma, Sp,
            rhoProjection, Sp, Eq, Sp, sigmaProjection, Sp, Iff, Sp,
            Forall, Sp, time, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Forall, Sp, effectIndex, InMacro, Sp,
            Call("Fin", Seq(r, Sp, Plus, Sp, D(1))), Comma, Sp,
            rhoExpectation, Sp, Eq, Sp, sigmaExpectation, Dot));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The canonical predictive projection is equivalent to all future statistics.",
            H("All Future Statistics Sufficiency"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("all-future-statistics-sufficiency"),
                    DeclarationHandle.Create(
                        "D5/S3/Quantum/Fibers/AllFutureStatisticsSufficiency."
                            + "all_future_statistics_sufficiency"),
                    H("The predictive coordinate determines exactly every future expectation"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Work on the real vector space of traceless Hermitian matrices. "
                                + "A finite centered effect family and its finite Heisenberg "
                                + "iterates generate the final predictive subspace.")),
                        Paragraph(Text(
                            "The predictive coordinate is the canonical orthogonal projection "
                                + "onto that all-iterate span. Two centered state coordinates "
                                + "have equal projections exactly when every iterated centered "
                                + "effect has the same expectation on both coordinates.")),
                        Paragraph(Text(
                            "The proof imports the frozen carrier, predictive span, and "
                                + "projection. Projection equality is converted to orthogonality "
                                + "of the state difference, and span induction converts this to "
                                + "the complete family of future expectation equalities."))),
                    DescribeRole.Theorem))));
    }
}
