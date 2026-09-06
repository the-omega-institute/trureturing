using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Accounting;

internal sealed class GeneralCarrierClerkInequalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fresh permanent records bound arbitrary semantic snapshots in ENat.",
        H("General-Carrier Clerk Inequalities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("general-carrier-clerk-inequalities"),
                DeclarationHandle.Create(
                    "D5/S0/History/Accounting/GeneralCarrierClerkInequality.clerk_inequality"),
                H("The two inequalities on arbitrary sets"),
                StatementSource.FromAuthor(InequalityFormula(false)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "SetClerkHistory extends the existing LedgerHistory enrollment and "
                        + "grading carrier. A statement is semantic at t exactly when it is "
                        + "enrolled by t and its grade is outside theoremGrade. It migrates "
                        + "at t exactly when it is semantic at t and has a theorem grade at "
                        + "t + 1. Semantic, migration, and record snapshots are arbitrary sets.")),
                    Paragraph(Text(
                        "The history certificate requires every record at t to be newly "
                        + "enrolled after t and semantic at every u at least t + 1. It also "
                        + "requires encard(recordsAt(t)) to be at least r times "
                        + "encard(migrationsAt(t)). The coefficient r is a natural number; "
                        + "r minus one is computed in Nat before coercion to ENat.")),
                    Paragraph(Text(
                        "Here cumulativeMigrations(H,t) is the ENat sum of "
                        + "encard(migrationsAt(H,i)) over i in Finset.range(t). ENat is "
                        + "the extended natural numbers and encard is Set.encard. "
                        + "No countability of statements, finiteness or order on grades, "
                        + "or upper closure of theoremGrade is required.")),
                    Paragraph(Text(
                        "Freshness and permanence prove that record batches at distinct ticks "
                        + "are disjoint. The cumulative_record_bound lemma places the sum of "
                        + "all earlier record encards below the current semantic encard. "
                        + "Combining it with the quotas proves the first clause. For the "
                        + "second clause, semantic_step_bound partitions the previous "
                        + "snapshot into migrants and survivors, adds disjoint fresh records, "
                        + "and cumulative_step_bound iterates the estimate.")),
                    Paragraph(Text(
                        "Repository and pinned Mathlib searches found the finite ClerkHistory "
                        + "owner and the general set-cardinality primitives, but no complete "
                        + "general-carrier clerk theorem. The derivation uses "
                        + "Set.encard_sdiff_add_encard_of_subset, Set.encard_union_eq, "
                        + "Set.encard_iUnion_of_finite, Finset.sum_le_sum, and "
                        + "Finset.sum_range_succ. The accounting statement is repo-derived."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-clerk-specialization"),
                DeclarationHandle.Create(
                    "D5/S0/History/Accounting/GeneralCarrierClerkInequality.finite_clerk_inequality"),
                H("Specialization to the finite owner"),
                StatementSource.FromAuthor(InequalityFormula(true)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here ClerkHistory and cumulativeMigrations are the frozen finite "
                        + "definitions in ClerkInequality, and card is Finset.card. The map "
                        + "ofFinite coerces all three snapshots to sets and preserves the "
                        + "same enrollment, grading, and accounting certificate. Applying "
                        + "the general theorem and reflecting ENat inequalities between "
                        + "natural casts yields exactly the two conclusions of the finite "
                        + "clerk_inequality owner. The proof consumes the general theorem."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/History/LedgerLimit")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S0/History/Accounting/ClerkInequality")),
        ]));

    private static Formula Call(string name, params Formula[] arguments) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Join(Comma, arguments), Close);

    private static Formula Join(Formula separator, Formula[] arguments) =>
        Seq(arguments.SelectMany((argument, index) =>
            index == 0 ? new[] { argument } : new[] { separator, Sp, argument }).ToArray());

    private static Formula InequalityFormula(bool finite)
    {
        Formula statement = F.Id("S");
        Formula grade = F.Id("G");
        Formula history = F.Id("H");
        Formula r = F.Id("r");
        Formula t = F.Id("t");
        Formula u = F.Id("u");
        Formula v = F.Id("v");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula enat = Seq(Operatorname, Grp(F.Id("ENat")));
        Formula count = Call("cumulativeMigrations", history, t);
        Formula size = Call(finite ? "card" : "encard", Call("semanticAt", history, t));
        Formula initial = Call(finite ? "card" : "encard", Call("semanticAt", history, D(0)));
        Formula coefficient = finite ? r : Seq(Open, r, Colon, Sp, enat, Close);
        Formula predecessor = Seq(Open, r, Sp, Minus, Sp, D(1), Colon, Sp, naturals, Close);
        if (!finite)
        {
            predecessor = Seq(Open, predecessor, Colon, Sp, enat, Close);
        }

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, u, Comma, Sp, v, Colon, Sp,
                Operatorname, Grp(F.Id("Level")), Comma, Sp,
                Forall, Sp, statement, Colon, Sp, Call("Type", u), Comma, Sp,
                grade, Colon, Sp, Call("Type", v), Comma),
            Seq(Forall, Sp, r, Comma, Sp, t, InMacro, Sp, naturals, Comma, Sp,
                Forall, Sp, history, Colon, Sp,
                Call(finite ? "ClerkHistory" : "SetClerkHistory", statement, grade, r), Comma),
            Seq(r, Sp, Geq, Sp, D(1), Sp, Rightarrow, Sp,
                Open, coefficient, Sp, Cdot, Sp, count, Sp, Leq, Sp, size),
            Seq(Land, Sp, initial, Sp, Plus, Sp, predecessor, Sp, Cdot, Sp,
                count, Sp, Leq, Sp, size, Close),
        ]));
    }
}
