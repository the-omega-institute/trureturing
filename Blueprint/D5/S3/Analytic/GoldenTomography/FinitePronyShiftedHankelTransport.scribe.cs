using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FinitePronyShiftedHankelTransportDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/GoldenTomography/FinitePronyShiftedHankelTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every shifted finite Prony Hankel section uses one fixed Vandermonde "
            + "observation map while elapsed time acts on diagonal modal weights.",
        H("Finite Prony Shifted Hankel Transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prony-shifted-hankel-factorization"),
                DeclarationHandle.Create(
                    Prefix + "finite_prony_shifted_hankel_factorization"),
                H("Every shifted Prony Hankel section has a Vandermonde factorization"),
                StatementSource.FromAuthor(ShiftFactorizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite exponential moment sequence, the Hankel section beginning "
                            + "at any observation-time shift factors through the same rectangular "
                            + "Vandermonde matrix on both sides.")),
                    Paragraph(Text(
                        "The shift appears only in the diagonal entries m_j q_j^shift. This "
                            + "extends the source's unshifted factorization (1295.6) to a complete "
                            + "finite family of shifted Hankel sections.")),
                    Paragraph(Text(
                        "The statement is exact and finite-dimensional. It supplies no noisy "
                            + "singular-value bound or infinite-delay convergence theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-prony-shifted-hankel-successor-transport"),
                DeclarationHandle.Create(
                    Prefix + "finite_prony_shifted_hankel_succ_transport"),
                H("One time step multiplies each hidden modal weight by its node"),
                StatementSource.FromAuthor(SuccTransportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Advancing the Hankel origin by one sample retains the observation map "
                            + "and multiplies the hidden weight of mode j by q_j.")),
                    Paragraph(Text(
                        "This is the exact diagonal transport interface used by matrix-pencil "
                            + "identification and finite Koopman spectral models. Eigenvalue "
                            + "recovery requires additional invertibility and separation results."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-prony-modal-shifts-compose"),
                DeclarationHandle.Create(
                    Prefix + "finite_prony_shifted_weights_add"),
                H("Modal observation-time shifts compose multiplicatively"),
                StatementSource.FromAuthor(WeightsAddFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Adding two observation-time shifts multiplies the current hidden modal "
                            + "weight by the corresponding power of its transport node. The "
                            + "identity isolates the semigroup law on each finite spectral fiber."))),
                DescribeRole.Theorem)),
        []));

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

    private static Formula Sub(string name, string idx) =>
        Seq(F.Id(name), Underscore, Grp(F.Id(idx)));

    private static Formula ShiftFactorizationFormula() => Disp(Seq(
        Sub("H", "s"), Open, F.Id("c"), Close, Sp, Eq, Sp,
        Call("V", F.Id("x")), Cdot,
        Call("D", Sub("w", "s")), Cdot,
        Call("V", F.Id("x")), Caret, Grp(F.Id("T"))));

    private static Formula SuccTransportFormula() => Disp(Seq(
        Seq(F.Id("H"), Underscore, Grp(Seq(F.Id("s"), Plus, D(1)))),
        Open, F.Id("c"), Close, Sp, Eq, Sp,
        Call("V", F.Id("x")), Cdot,
        Call("D", Seq(Sub("w", "s"), Cdot, Sp, F.Id("x"))), Cdot,
        Call("V", F.Id("x")), Caret, Grp(F.Id("T"))));

    private static Formula WeightsAddFormula() => Disp(Seq(
        Seq(F.Id("w"), Underscore, Grp(Seq(F.Id("a"), Plus, F.Id("b")))),
        Open, F.Id("j"), Close, Sp, Eq, Sp,
        Sub("w", "a"), Open, F.Id("j"), Close, Cdot, Sp, Sub("x", "j"), Caret, Grp(F.Id("b"))));
}
