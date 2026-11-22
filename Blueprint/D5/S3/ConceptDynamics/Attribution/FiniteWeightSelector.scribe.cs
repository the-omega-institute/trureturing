using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class FiniteWeightSelectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Singleton weight fibers characterize admissible deterministic selection under label permutations.",
        H("Equivariant selection from finite weight profiles"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-weight-selector-iff"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Attribution/FiniteWeightSelector.exists_equivariant_selector_iff"),
            H("An equivariant selector exists exactly when each profile has an admissible singleton weight"),
            StatementSource.FromAuthor(SelectorFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let I be a finite label type and R a linearly ordered weight type. "
                        + "A permutation g acts by composing a profile with the inverse of g. "
                        + "The set D of profiles is closed under this action, "
                        + "and each permutation carries admissible labels to admissible labels and conversely. "
                        + "Every profile in D then admits an equivariant deterministic choice in a common rule "
                        + "exactly when each profile has an admissible label whose weight occurs exactly once.")),
                Paragraph(Text(
                    "If another label has the selected label's weight, their transposition preserves the entire "
                        + "profile and moves the selected label. This contradicts equivariance. Conversely, "
                        + "choose the greatest weight among admissible labels with singleton weight fibers. "
                        + "Finiteness gives a greatest weight, and its singleton fiber gives a unique label. "
                        + "Permuting labels carries the eligible set to the new eligible set and preserves the "
                        + "maximum weight, so it also transports the selected label.")),
                Paragraph(Text(
                    "For binary normalized weights with both labels admissible, this recovers the exclusion of "
                        + "the equal-weight pair. In a three-outcome test with weights (2/5, 2/5, 1/5), all labels "
                        + "admissible permits the unique 1/5 label. If admissibility requires a maximum weight, "
                        + "existence instead requires a unique maximum in each profile, which this test lacks."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula SelectorFormula()
    {
        Formula domain = F.Id("D");
        Formula allowed = F.Id("Allowed");
        Formula weight = F.Id("w");
        Formula label = F.Id("i");
        Formula other = F.Id("j");
        Formula choose = F.Id("s");
        Formula perm = F.Id("g");
        Formula labels = F.Id("I");
        Formula weights = F.Id("R");
        Formula profile = new Formula.TypeArrow(labels, weights);
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula perms = Call("Perm", labels);
        Formula reindex = Call("permute", perm, weight);
        Formula invariant = Seq(Forall, Sp, perm, InMacro, Sp, perms, Comma, Sp,
            Forall, Sp, weight, InMacro, Sp, domain, Comma, Sp, reindex, InMacro, Sp, domain);
        Formula admissibility = Seq(Forall, Sp, perm, InMacro, Sp, perms, Comma, Sp,
            Forall, Sp, weight, Colon, profile, Comma, Sp,
            Forall, Sp, label, InMacro, Sp, labels, Comma, Sp,
            Call("Allowed", reindex, Call("g", label)), Sp, Iff, Sp,
            Call("Allowed", weight, label));
        Formula covariant = Seq(Forall, Sp, perm, InMacro, Sp, Call("Perm", labels), Comma, Sp,
            Forall, Sp, weight, InMacro, Sp, domain, Comma, Sp,
            Call("s", reindex), Eq, Call("g", Call("s", weight)));
        Formula eligible = Seq(Forall, Sp, weight, InMacro, Sp, domain, Comma, Sp,
            Call("Allowed", weight, Call("s", weight)));
        Formula singleton = Seq(Forall, Sp, other, InMacro, Sp, labels, Comma, Sp,
            Call("w", other), Eq, Call("w", label), Rightarrow, Sp, other, Eq, label);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, labels, Comma, weights, Colon, type, Comma, Sp,
            OpenBracket, Call("Fintype", labels), CloseBracket, Sp,
            OpenBracket, Call("LinearOrder", weights), CloseBracket, Comma, RowBreak,
            Forall, Sp, domain, Colon, Call("Set", profile), Comma, Sp, allowed, Colon,
            new Formula.TypeArrow(profile, new Formula.TypeArrow(labels, F.Id("Prop"))),
            Comma, RowBreak,
            Open, invariant, Close, Sp, Land, Sp, Open, admissibility, Close, Sp, Rightarrow, RowBreak, Grp(),
            OpenBracket, Open, Exists, Sp, choose, Colon, new Formula.TypeArrow(domain, labels), Comma, Sp,
            Open, eligible, Close, Sp, Land, Sp, Open, covariant, Close,
            Close, Sp, Iff, RowBreak,
            Forall, Sp, weight, InMacro, Sp, domain, Comma, Sp,
            Exists, Sp, label, InMacro, Sp, labels, Comma, Sp,
            Call("Allowed", weight, label), Sp, Land, Sp, Open, singleton, Close, CloseBracket,
            End, Grp(F.Id("gathered"))));
    }
}
