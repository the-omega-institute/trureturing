using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class PublicLedgerDescentDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix = "D5/S3/QuantumContext/PublicLedgerDescent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Public overlap compatibility is exactly descent to one noncontextual additive valuation.",
        H("Public Ledger Descent Across Overlapping Contexts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("publicness-transports-an-additive-decomposition-between-contexts"),
                DeclarationHandle.Create(LeanPrefix + "public_ledger_cross_context_additivity"),
                H("Publicness transports additive decompositions between contexts"),
                StatementSource.FromAuthor(CrossContextFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose context c displays an event w as the declared disjoint "
                            + "coarse-graining of events a and b, and context d also displays w. "
                            + "The additive law in c gives L_c(w)=L_c(a)+L_c(b). Publicness then "
                            + "identifies L_d(w) with L_c(w), yielding the displayed equality "
                            + "across two contexts.")),
                    Paragraph(Text(
                        "Unlike a finite sum-union identity, this conclusion names two context "
                            + "rows and changes the presentation of the unchanged coarse event. "
                            + "Its proof uses both the public overlap law and the source context's "
                            + "valuation law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("public-compatible-context-valuations-glue-uniquely"),
                DeclarationHandle.Create(LeanPrefix + "public_ledger_descent_iff"),
                H("Public compatible context valuations glue uniquely"),
                StatementSource.FromAuthor(DescentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E_cov contain exactly the events presented by at least one context. "
                            + "A public, contextwise additive family L_c determines one valuation "
                            + "mu on E_cov: choose any context containing an event and read its "
                            + "ledger entry. Publicness proves that the result is independent of "
                            + "the chosen context. Restriction to E_cov makes uniqueness exact; no "
                            + "arbitrary values are assigned to events outside the experiment.")),
                    Paragraph(Text(
                        "Every local decomposition law transports through the restriction "
                            + "equalities, so the single valuation is additive on every context. "
                            + "Conversely, restrictions of one global valuation automatically "
                            + "agree on overlaps, and its contextual additive law recovers each "
                            + "local additive law. Thus publicness plus local additivity is "
                            + "equivalent to unique noncontextual additive descent.")),
                    Paragraph(Text(
                        "This is the pre-Gleason bridge claimed by the source atoms. Additivity is "
                            + "an explicit premise on context valuations and becomes noncontextual "
                            + "through descent; the theorem asserts no positivity, Gleason "
                            + "representation, Born-rule uniqueness, or solution-space result."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-projection-events-descend-to-one-additive-valuation"),
                DeclarationHandle.Create(LeanPrefix + "projection_public_ledger_descent"),
                H("Finite projection events descend to one additive valuation"),
                StatementSource.FromAuthor(ProjectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each frozen measurement context, the event support is the powerset "
                            + "of its four actual ConfigurationProjection values. A declared "
                            + "decomposition W=A union B requires A and B to be disjoint, so union "
                            + "is a genuine projection-event coarse-graining operation rather than "
                            + "an equality between unrelated bookkeeping sums.")),
                    Paragraph(Text(
                        "Applying the generic equivalence says that public additive rows on all "
                            + "nine projection contexts are precisely the restrictions of one "
                            + "unique valuation on every projection event that occurs. This does "
                            + "not alter or reprove the frozen binary valuation obstruction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compatible-overlapping-contexts-descend-nontrivially"),
                DeclarationHandle.Create(LeanPrefix + "overlapping_context_ledger_witness"),
                H("Compatible overlapping contexts descend nontrivially"),
                StatementSource.FromAuthor(CompatibleWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The distinct contexts {0,1} and {1,2} share the singleton event {1}. "
                            + "Their atomic rows are (2/3,1/3) and (1/3,2/3), so both totals are "
                            + "one and both presentations give the shared atom value 1/3. Event "
                            + "values are finite sums of these atomic entries and hence satisfy "
                            + "the declared disjoint-union laws.")),
                    Paragraph(Text(
                        "The theorem proves publicness and local additivity, then obtains a unique "
                            + "global valuation from the descent equivalence. The local valuation "
                            + "functions are distinct, so the witness is genuinely overlapping and "
                            + "nonconstant rather than a duplicated context row."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("incompatible-overlapping-contexts-do-not-descend"),
                DeclarationHandle.Create(LeanPrefix + "incompatible_overlapping_contexts_do_not_descend"),
                H("Incompatible overlapping contexts do not descend"),
                StatementSource.FromAuthor(IncompatibleWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Keep the same overlapping supports and normalized locally additive event "
                            + "rows, but assign the shared atom value 1/3 in the first context and "
                            + "2/3 in the second. Any global restriction would give the singleton "
                            + "event {1} one value, forcing those unequal numbers to coincide.")),
                    Paragraph(Text(
                        "This counterexample isolates the load-bearing premise: normalization and "
                            + "contextwise additivity alone do not produce a noncontextual global "
                            + "valuation. Publicness is exactly the missing gluing condition."))),
                DescribeRole.Theorem))));

    private static Formula CrossContextFormula() => Disp(Seq(
        Operatorname, Grp(F.Id("Public")), Open, F.Id("L"), Close, Sp, Land, Sp,
        Operatorname, Grp(F.Id("Add")), Underscore, Grp(F.Id("C")), Open, F.Id("L"), Close,
        Sp, Rightarrow, Sp,
        Forall, Sp, F.Id("c"), Comma, Sp, F.Id("d"), Comma, Sp,
        F.Id("w"), Comma, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Comma, Esc,
        F.Id("w"), Comma, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Sp, InMacro, Sp,
        F.Id("C"), Underscore, Grp(F.Id("c")), Sp, Land, Sp,
        F.Id("w"), InMacro, Sp, F.Id("C"), Underscore, Grp(F.Id("d")), Sp, Land, Sp,
        F.Id("w"), Eq, F.Id("a"), Sp, Operatorname, Grp(F.Id("disjoint"), Sp, F.Id("union")), Sp,
        F.Id("b"), Sp, Rightarrow, Sp,
        F.Id("L"), Underscore, Grp(F.Id("d")), Open, F.Id("w"), Close, Eq,
        F.Id("L"), Underscore, Grp(F.Id("c")), Open, F.Id("a"), Close, Plus,
        F.Id("L"), Underscore, Grp(F.Id("c")), Open, F.Id("b"), Close, Dot));

    private static Formula DescentFormula() => Disp(Seq(
        Operatorname, Grp(F.Id("Public")), Open, F.Id("L"), Close, Sp, Land, Sp,
        Operatorname, Grp(F.Id("Add")), Underscore, Grp(F.Id("C")), Open, F.Id("L"), Close,
        Sp, Iff, Sp,
        Exists, Bang, Sp, Mu, Colon, Sp,
        F.Id("E"), Underscore, Grp(Mathrm, Grp(F.Id("cov"))), To, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
        Open, Forall, Sp, F.Id("c"), Comma, Sp, F.Id("e"), InMacro, Sp,
        F.Id("C"), Underscore, Grp(F.Id("c")), Comma, Esc,
        Mu, Open, F.Id("e"), Close, Eq,
        F.Id("L"), Underscore, Grp(F.Id("c")), Open, F.Id("e"), Close, Close,
        Sp, Land, Sp,
        Operatorname, Grp(F.Id("Add")), Underscore, Grp(F.Id("C")), Open, Mu, Close, Dot));

    private static Formula ProjectionFormula() => Disp(Seq(
        Operatorname, Grp(F.Id("Public")), Open, F.Id("L"), Close, Sp, Land, Sp,
        Operatorname, Grp(F.Id("Add")), Underscore, Grp(F.Id("projection"), Sp, F.Id("contexts")),
        Open, F.Id("L"), Close, Sp, Iff, Sp,
        Exists, Bang, Sp, Mu, Colon, Sp,
        F.Id("E"), Underscore, Grp(Mathrm, Grp(F.Id("proj"), Comma, F.Id("cov"))), To, Sp,
        Mathbb, Grp(F.Id("R")), Comma, Esc,
        Operatorname, Grp(F.Id("Restrict")), Open, Mu, Close, Eq, F.Id("L"), Sp, Land, Sp,
        Operatorname, Grp(F.Id("Add")), Underscore, Grp(F.Id("projection"), Sp, F.Id("contexts")),
        Open, Mu, Close, Dot));

    private static Formula CompatibleWitnessFormula() => Disp(Seq(
        F.Id("C"), Underscore, Grp(D(0)), Eq, OpenBrace, D(0), Comma, D(1), CloseBrace,
        Comma, Sp, F.Id("C"), Underscore, Grp(D(1)), Eq,
        OpenBrace, D(1), Comma, D(2), CloseBrace, Comma, Esc,
        F.Id("L"), Underscore, Grp(D(0)), OpenBrace, D(1), CloseBrace, Eq,
        Frac, Grp(D(1)), Grp(D(3)), Eq,
        F.Id("L"), Underscore, Grp(D(1)), OpenBrace, D(1), CloseBrace, Comma, Esc,
        Operatorname, Grp(F.Id("Public")), Open, F.Id("L"), Close, Sp, Land, Sp,
        Operatorname, Grp(F.Id("Add")), Underscore, Grp(F.Id("C")), Open, F.Id("L"), Close,
        Sp, Land, Sp, Exists, Bang, Sp, Mu, Comma, Esc,
        Operatorname, Grp(F.Id("Restrict")), Open, Mu, Close, Eq, F.Id("L"), Sp, Land, Sp,
        Operatorname, Grp(F.Id("Add")), Underscore, Grp(F.Id("C")), Open, Mu, Close, Dot));

    private static Formula IncompatibleWitnessFormula() => Disp(Seq(
        Open, Forall, Sp, F.Id("c"), Comma, Esc,
        F.Id("L"), Underscore, Grp(F.Id("c")), Open,
        F.Id("C"), Underscore, Grp(F.Id("c")), Close, Eq, D(1), Close, Sp, Land, Sp,
        Operatorname, Grp(F.Id("Add")), Underscore, Grp(F.Id("C")), Open, F.Id("L"), Close,
        Sp, Land, Sp, Neg, Exists, Sp, Mu, Comma, Esc,
        Operatorname, Grp(F.Id("Restrict")), Open, Mu, Close, Eq, F.Id("L"), Dot));
}
