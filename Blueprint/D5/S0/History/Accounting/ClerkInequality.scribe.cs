using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Accounting;

internal sealed class ClerkInequalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Permanent records force two lower bounds on the semantic ledger.",
        H("The Clerk Inequalities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("permanent-records-force-the-clerk-inequalities"),
                DeclarationHandle.Create(
                    "D5/S0/History/Accounting/ClerkInequality.clerk_inequality"),
                H("Permanent records force the clerk inequalities"),
                StatementSource.FromAuthor(ClerkInequalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let H be a finite counting certificate over an append-only ledger. "
                            + "Its semantic snapshot contains exactly the enrolled statements "
                            + "outside the distinguished theorem grades, and its migration "
                            + "snapshot contains exactly the statements entering those grades "
                            + "at the next tick.")),
                    Paragraph(Text(
                        "Every migration creates at least r fresh records. Each record is newly "
                            + "enrolled at its creation tick and remains in every later semantic "
                            + "snapshot. When r is at least one, the semantic count at tick t is "
                            + "therefore at least r times the cumulative migration count. It is "
                            + "also at least the initial semantic count plus r minus one times "
                            + "the cumulative migration count.")),
                    Paragraph(Text(
                        "The first bound counts the disjoint permanent records. The second removes "
                            + "the migrating statements from the old snapshot, inserts the fresh "
                            + "records, and iterates the resulting one-step bound. Pinned Mathlib "
                            + "and Loogle supplied Finset.sum_range_succ, which is imported and "
                            + "applied to both cumulative counts. Repository searches found no "
                            + "existing declaration with either complete bound; LeanSearch's "
                            + "query endpoint returned HTTP 404."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/History/LedgerLimit")),
        ]));

    private static Formula ClerkInequalityFormula()
    {
        Formula r = F.Id("r");
        Formula t = F.Id("t");
        Formula history = F.Id("H");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula migrations = new Formula.Subscript(F.Id("M"), t);
        Formula semanticAtT = Seq(
            Lvert, Sp, new Formula.Subscript(F.Id("Sem"), t), Rvert);
        Formula semanticAtZero = Seq(
            Lvert, Sp, new Formula.Subscript(F.Id("Sem"), D(0)), Rvert);

        return Disp(Seq(
            Forall, Sp, r, Comma, Sp, t, InMacro, Sp, naturals, Comma, Sp,
            Forall, Sp, history, Colon, Sp,
            Operatorname, Grp(F.Id("ClerkHistory")), Open, r, Close, Comma, Sp,
            r, Sp, Geq, Sp, D(1), Sp, Rightarrow, Sp,
            Left, Open, new Formula.Aligned([
                Seq(semanticAtT, Sp, Geq, Sp, r, Sp, Cdot, Sp, migrations),
                Seq(Land, Sp, semanticAtT, Sp, Geq, Sp, semanticAtZero,
                    Sp, Plus, Sp, Open, r, Sp, Minus, Sp, D(1), Close,
                    Sp, Cdot, Sp, migrations),
            ]), Right, Close, Dot));
    }
}
