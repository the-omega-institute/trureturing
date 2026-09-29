using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class LocalMarginalCorrelationBlindSpotDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula two = D(2);
        Formula mSquared = new Formula.Power(m, two);
        Formula nSquared = new Formula.Power(n, two);
        Formula local = F.Id("L");
        Formula correlation = F.Id("C");
        Formula traceZero = new Formula.Subscript(F.Id("H"), D(0));
        Formula firstRank = Seq(mSquared, Sp, Minus, Sp, D(1));
        Formula secondRank = Seq(nSquared, Sp, Minus, Sp, D(1));
        Formula correlationRank = Seq(Open, firstRank, Close, Open, secondRank, Close);
        Formula totalRank = Seq(mSquared, nSquared, Sp, Minus, Sp, D(1));
        Formula bell = Rho;
        Formula classical = SigmaLower;
        Formula classicalSquared = new Formula.Power(classical, two);
        // Escaped spaces preserve row breaks through Markdown parsing.
        Formula statement = Disp(Seq(Nl,
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, m, Comma, Sp, n, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
            Comma, RowBreak, Esc, Grp(),
            m, Sp, Geq, Sp, D(1), Sp, Land, Sp,
            n, Sp, Geq, Sp, D(1), Sp, Land, Sp,
            m, n, Sp, Gt, Sp, D(1), Sp, Rightarrow, RowBreak, Esc, Grp(),
            local, Sp, Plus, Sp, correlation, Sp, Eq, Sp, traceZero,
            Sp, Land, RowBreak, Esc, Grp(),
            Apply("dim", local), Sp, Eq, Sp,
            Open, firstRank, Close, Sp, Plus, Sp, Open, secondRank, Close,
            Sp, Land, RowBreak, Esc, Grp(),
            Apply("dim", correlation), Sp, Eq, Sp, correlationRank,
            Sp, Land, RowBreak, Esc, Grp(),
            Frac, Grp(Apply("dim", correlation)), Grp(Apply("dim", traceZero)),
            Sp, Eq, Sp, Frac, Grp(correlationRank), Grp(totalRank),
            Sp, Land, RowBreak, Esc, Grp(),
            local, Sp, Perp, Sp, correlation,
            Sp, Land, RowBreak, Esc, Grp(),
            bell, Sp, Geq, Sp, D(0), Sp, Land, Sp,
            Apply("Tr", bell), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Apply("rank", bell), Sp, Eq, Sp, D(1),
            Sp, Land, RowBreak, Esc, Grp(),
            classical, Sp, Geq, Sp, D(0), Sp, Land, Sp,
            Apply("Tr", classical), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            classicalSquared, Sp, Neq, Sp, classical,
            Sp, Land, RowBreak, Esc, Grp(),
            PartialTrace("B", bell), Sp, Eq, Sp, PartialTrace("B", classical),
            Sp, Land, RowBreak, Esc, Grp(),
            PartialTrace("A", bell), Sp, Eq, Sp, PartialTrace("A", classical),
            Sp, Land, RowBreak, Esc, Grp(),
            bell, Sp, Neq, Sp, classical, Dot,
            End, Grp(F.Id("gathered")), Nl));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Complete local marginals leave every cross-factor correlation direction unread.",
            H("The Correlation Blind Spot of Local Marginals"),
            Blocks(
                Paragraph(
                    Text("In the real Hermitian tensor model with factor dimensions "),
                    Math(In(Seq(m, Comma, Sp, n))), Text(", write "), Math(In(local)),
                    Text(" for the sum of the canonical traceless local sectors, "),
                    Math(In(correlation)), Text(" for the sector traceless in both factors, and "),
                    Math(In(traceZero)), Text(" for the full traceless space. "
                        + "Sector dimensions and orthogonality are real.")),
                Paragraph(
                    Text("Independently, "), Math(In(bell)),
                    Text(" is the canonical two-qubit Bell density for 00 and 11, and "),
                    Math(In(classical)), Text(" their equal diagonal mixture. Here "),
                    Math(In(Seq(Geq, Sp, D(0)))), Text(" means positive semidefinite; "),
                    Text("partial-trace subscripts name the factor traced out.")),
                Describe.Lean(
                    DescribeId.Create("local-marginal-correlation-blind-spot"),
                    DeclarationHandle.Create(
                        "D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot."
                            + "local_marginal_correlation_blind_spot"),
                    H("Complete local data omit the full correlation sector"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The correlation sector is orthogonal to all local directions. "
                                + "The ratio gives its share of the traceless space.")),
                        Paragraph(Text(
                            "The fixed witness has identical local marginals but different "
                                + "global matrices: complete local data need not determine "
                                + "cross-factor correlations."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Apply(string name, Formula argument) =>
        Seq(Mathrm, Grp(F.Id(name)), Open, argument, Close);

    private static Formula PartialTrace(string factor, Formula argument) =>
        Seq(new Formula.Subscript(Seq(Mathrm, Grp(F.Id("Tr"))), F.Id(factor)),
            Open, argument, Close);
}
