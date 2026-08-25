using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.Cocycles;

internal sealed class ExtensionSectionCoboundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An additive section exists exactly when the canonical kernel carry is a coboundary.",
        H("Section Coboundary Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("section-exists-iff-carry-is-a-coboundary"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Cocycles/ExtensionSectionCoboundary."
                        + "extension_section_iff_coboundary"),
                H("Section existence and the carry coboundary criterion"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For additive commutative groups X and B, q is an additive quotient "
                            + "map and s is a set-theoretic right inverse with s(0)=0. The "
                            + "kernel-valued carry is the existing canonical construction, "
                            + "and the displayed coboundary is formed from a map beta into "
                            + "that kernel.")),
                    Paragraph(Text(
                        "A homomorphic right-inverse section exists exactly when the carry "
                            + "is cancelled by such a coboundary. Consequently, absence of "
                            + "a coboundary witness rules out every additive section."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula TheoremFormula()
    {
        Formula x = F.Id("X");
        Formula b = F.Id("B");
        Formula quotient = F.Id("q");
        Formula representative = F.Id("r");
        Formula section = Seq(F.Id("s"), Apos);
        Formula beta = F.Id("beta");
        Formula a = F.Id("a");
        Formula c = F.Id("b");
        Formula sectionExists = Seq(
            Exists, Sp, section, Colon, Sp, Call("AddMonoidHom", b, x), Comma, Sp,
            Call("RightInverse", section, quotient));
        Formula betaExists = Seq(
            Exists, Sp, beta, Colon, Sp, b, Sp, To, Sp, Apply("ker", quotient), Comma, Sp,
            Forall, Sp, a, Comma, Sp, c, InMacro, Sp, b, Comma, Sp,
            Apply("kernelCarry", quotient, representative, a, c), Sp, Plus, Sp,
            Apply("additiveCoboundary", quotient, beta, a, c), Sp, Eq, Sp, D(0));

        Formula hypotheses = Seq(
            Call("AddCommGroup", x), Sp, Land, Sp,
            Call("AddCommGroup", b), Sp, Land, Sp,
            quotient, Colon, Sp, Call("AddMonoidHom", x, b), Sp, Land, Sp,
            representative, Colon, Sp, b, Sp, To, Sp, x, Sp, Land, Sp,
            Call("RightInverse", representative, quotient), Sp, Land, Sp,
            Apply("r", D(0)), Sp, Eq, Sp, D(0));

        Formula conclusion = new Formula.Logic(
            new Formula.Logic(sectionExists, FormulaLogicOperator.Iff, betaExists),
            FormulaLogicOperator.And,
            new Formula.Logic(new Formula.Not(betaExists), FormulaLogicOperator.Implies,
                new Formula.Not(sectionExists)));

        return Disp(Seq(
            Forall, Sp, x, Comma, Sp, b, Comma, Sp,
            quotient, Comma, Sp, representative, Comma, Sp,
            hypotheses, Sp, Rightarrow, Sp, conclusion, Dot));
    }
}
