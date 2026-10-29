using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Agency;

internal sealed class MinimumInstalledReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The attained minimum effective installed alphabet for arbitrary finite configuration families.",
        H("Minimum Installed Readout"),
        Blocks(Describe.Lean(
            DescribeId.Create("minimum-installed-readout"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Agency/MinimumInstalledReadout.installed_readout_optimum"),
            H("Sink labels plus an actual minimum enabled-event hitting set"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For the finite insertion model, sinks F contains the operational sinks. Hits F H means that H contains an enabled event for every nonsink. The number tau is the least cardinality of a hitting set, defined by minimization over natural numbers. The full event set hits every nonempty enabled set, so this minimum exists. The theorem includes both a minimizing set and its universal minimality property.")),
                Paragraph(Text("effectiveSize r is the cardinality of the actual image of r on F, regardless of its symbol carrier. For an arbitrary successful history policy, each sink has a private symbol. Every other effective fiber has a common enabled event, including singleton nonsinks. Choosing one event per such fiber produces a hitting set whose size is no larger than the number of those fibers. This proves the lower bound for unrestricted history policies.")),
                Paragraph(Text("For attainment, choose a minimum hitting set H and, at each nonsink C, choose one event in H enabled at C. Give a sink its own left label C and a nonsink the right label of its selected event. The two label families are disjoint. Each right-label fiber has a common enabled event, and every sink label is private. The finite acquisition criterion constructs the actual finite-table policy and proves the addition bound. Its effective image has at most card T plus card H symbols; the lower bound forces equality.")),
                Paragraph(Text("The family may be disconnected and need not contain the empty configuration or any root. The empty event type, a singleton family, and an all-sink family are included. If every state is a sink, the empty hitting set has minimum size zero and the readout directly identifies each state. Only the number of effective installed symbols is minimized. Same-run recovery of an earlier state, source transport and physical implementation require their own interfaces."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Card(Formula a) => Seq(Lvert, Sp, a, Rvert, Sp);
    private static Formula Statement()
    {
        Formula e = F.Id("E"), family = F.Id("F"), h = F.Id("H"), k = F.Id("K");
        Formula q = F.Id("Q"), r = F.Id("r"), p = F.Id("p");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula tau = Call("hittingNumber", family);
        Formula value = Seq(Card(Call("sinks", family)), Plus, tau);
        Formula hitMinimum = Seq(
            Grp(Seq(Exists, Sp, h, Colon, Sp, Call("Finset", e), Comma, Sp,
                Call("Hits", family, h), Sp, Land, Sp, Card(h), Eq, tau)), Sp, Land, Sp,
            Grp(Seq(Forall, Sp, k, Colon, Sp, Call("Finset", e), Comma, Sp,
                Call("Hits", family, k), Sp, Implies, Sp, tau, Sp, Leq, Sp, Card(k))));
        Formula lower = Seq(Forall, Sp, q, Colon, Sp, type, Comma, Sp,
            r, Colon, Sp, Arrow(Call("State", family), q), Comma, Sp,
            Grp(Seq(Exists, Sp, p, Colon, Sp,
                Arrow(Call("History", e, q), Call("Decision", family)), Comma, Sp,
                Call("Acquires", r, p))), Sp, Implies, Sp,
            value, Sp, Leq, Sp, Call("effectiveSize", r));
        Formula attained = Seq(Exists, Sp, r, Colon, Sp,
            Arrow(Call("State", family), Call("Sum", Call("State", family), e)), Comma, Sp,
            Call("FiniteAcquirable", r), Sp, Land, Sp, Call("effectiveSize", r), Eq, value);
        return Disp(Seq(Forall, Sp, e, Colon, Sp, type, Comma, Sp,
            OpenBracket, Call("Fintype", e), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", e), CloseBracket, Comma, Sp,
            family, Colon, Sp, Call("Finset", Call("Finset", e)), Comma, Sp,
            Call("Nonempty", family), Sp, Implies, RowBreak, Grp(),
            Grp(hitMinimum), Sp, Land, Sp, Grp(lower), Sp, Land, Sp, Grp(attained), Dot));
    }
}
