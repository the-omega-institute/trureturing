using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming;

internal sealed class SkewedIndependentKillRateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var fixedPointMass = Seq(
            Sum, Underscore,
            Grp(F.Id("y"), Sp, InMacro, Sp, Call("Fix", F.Id("f"))), Sp,
            F.Id("q"), Open, F.Id("y"), Close);

        return DocumentDefinition.Create(ScribeNode.Create(
            "A finite behavior distribution replaces the uniform fixed fraction by weighted fixed-point mass.",
            H("Skewed Independent Kill Rate"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("skewed-independent-kill-rate"),
                    DeclarationHandle.Create(
                        "D5/S0/Naming/SkewedIndependentKillRate.skewed_independent_kill_rate"),
                    H("Weighted fixed mass skews the independent kill rate"),
                    StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Y"), Comma, Sp, F.Id("Outcome"), Comma, Sp,
                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("Y"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("MeasurableSpace")), Open,
                    F.Id("Outcome"), Close, Comma, Sp,
                    F.Id("q"), Colon, Sp,
                    Operatorname, Grp(F.Id("PMF")), Open, F.Id("Y"), Close,
                    Comma, Sp,
                    F.Id("f"), Colon, Sp, F.Id("Y"), Sp, To, Sp, F.Id("Y"),
                    Comma, Sp,
                    F.Id("mu"), Colon, Sp,
                    Operatorname, Grp(F.Id("Measure")), Open, F.Id("Outcome"), Close,
                    Comma, Sp,
                    F.Id("C"), Comma, Sp, F.Id("V"), Colon, Sp,
                    Operatorname, Grp(F.Id("Set")), Open, F.Id("Outcome"), Close,
                    Comma, Sp,
                    F.Id("coverageRate"), Colon, Sp, F.Id("ENNReal"), Comma, Sp,
                    Open,
                    Operatorname, Grp(F.Id("IndepSet")), Open,
                    F.Id("C"), Comma, Sp, F.Id("V"), Comma, Sp, F.Id("mu"), Close,
                    Sp, Land, Sp,
                    F.Id("mu"), Open, F.Id("C"), Close,
                    Sp, Eq, Sp, F.Id("coverageRate"),
                    Sp, Land, Sp,
                    F.Id("mu"), Open, F.Id("V"), Close,
                    Sp, Eq, Sp,
                    F.Id("escapeMass"), Open, F.Id("q"), Comma, Sp, F.Id("f"), Close,
                    Close, Sp, Rightarrow, Sp,
                    Open,
                    F.Id("escapeMass"), Open, F.Id("q"), Comma, Sp, F.Id("f"), Close,
                    Sp, Eq, Sp, D(1), Minus,
                    F.Id("fixedMass"), Open, F.Id("q"), Comma, Sp, F.Id("f"), Close,
                    Sp, Land, Sp,
                    F.Id("escapeMass"), Open, F.Id("q"), Comma, Sp, F.Id("f"), Close,
                    Sp, Eq, Sp, D(1), Minus, fixedPointMass,
                    Sp, Land, Sp,
                    F.Id("mu"), Open,
                    Operatorname, Grp(F.Id("inter")), Open,
                    F.Id("C"), Comma, Sp, F.Id("V"), Close, Close,
                    Sp, Eq, Sp,
                    F.Id("coverageRate"), Sp, Times, Sp,
                    Open, D(1), Minus,
                    F.Id("fixedMass"), Open, F.Id("q"), Comma, Sp, F.Id("f"), Close,
                    Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem exposes the fixed-point mass as the explicit finite sum "
                        + "sum_{y in Fix f} q(y), so the effective equivalent-mutant mass is q(Fix f), "
                        + "a distributional mass rather than an alphabet cardinality. Its complement "
                        + "is the visible mutation mass escapeMass.")),
                    Paragraph(Text(
                        "Let C be the coverage event and V the visibility event. The hypotheses say "
                        + "that C and V are independent, that C has the named coverage rate, and that "
                        + "V has the escape mass induced by q and f. The intersection is therefore "
                        + "the coverage rate multiplied by one minus the weighted fixed-point mass.")),
                    Paragraph(Text(
                        "The proof composes the frozen weighted complement law with the frozen "
                        + "independent event product law. Uniform behavior is not assumed. Multi-site "
                        + "mutations and regression-based estimation are outside this statement."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Asymptotics/SkewedEscapeMass")),
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Naming/IndependentKillRate")),
            ]));
    }
}
