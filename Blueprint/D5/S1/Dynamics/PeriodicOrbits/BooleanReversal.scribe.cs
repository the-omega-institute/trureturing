using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.PeriodicOrbits;

internal sealed class BooleanReversalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boolean negation gives every state exact period two.",
        H("Boolean Reversal Has Exact Period Two"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("boolean-reversal-has-exact-period-two"),
                DeclarationHandle.Create(
                    "D5/S1/Dynamics/PeriodicOrbits/BooleanReversal."
                        + "boolean_reversal_has_minimal_period_two"),
                H("Boolean reversal has exact period two"),
                StatementSource.FromAuthor(PeriodFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each Boolean state b, applying negation twice returns b, while "
                            + "a single negation never fixes b. Hence the minimal positive "
                            + "return time is exactly two.")),
                    Paragraph(Text(
                        "This closes qdo-v1 corollary/38.4, atom "
                            + "qdo-residual-8581f6063c025dfe2404a2a8064e7c04c67fe3091ca9821043e"
                            + "697a82f20e73e.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies the periodic-point minimal-period API and "
                            + "Bool.not_ne_self. Loogle returned no declaration for the query "
                            + "Function.minimalPeriod = 2, and repository search found no "
                            + "equivalent theorem."))),
                DescribeRole.Theorem))));

    private static Formula PeriodFormula()
    {
        Formula state = F.Id("b");
        Formula boolean = Seq(Mathbb, Grp(F.Id("B")));
        Formula reversal = Seq(Operatorname, Grp(F.Id("not")));
        Formula minimalPeriod = Seq(Operatorname, Grp(F.Id("minimalPeriod")));

        return Disp(Seq(
            Forall, Sp, state, Sp, InMacro, Sp, boolean, Comma, Esc,
            minimalPeriod, Open, reversal, Comma, Sp, state, Close,
            Sp, Eq, Sp, D(2), Dot));
    }
}
