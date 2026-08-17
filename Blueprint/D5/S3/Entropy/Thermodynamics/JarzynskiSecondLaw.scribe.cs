using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Thermodynamics;

internal sealed class JarzynskiSecondLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Jarzynski equality at positive inverse temperature bounds free-energy change " +
        "by mean work.",
        H("Jarzynski Equality and the Second Law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("jarzynski-equality-implies-the-mean-work-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Thermodynamics/JarzynskiSecondLaw.jarzynski_implies_second_law"),
                H("Jarzynski equality implies the mean-work bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("W"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Forall, Sp, Beta, Comma, Sp, Delta, Sp, F.Id("F"), InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("i")),
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1), Sp, Land, Sp,
                    D(0), Lt, Sp, Beta, Sp, Land, Sp, RowBreak,
                    Sum, Underscore, Grp(F.Id("i")),
                    F.Id("p"), Open, F.Id("i"), Close, Sp,
                    Exp, Grp(Minus, Beta, Sp, F.Id("W"), Open, F.Id("i"), Close),
                    Eq,
                    Exp, Grp(Minus, Beta, Sp, Delta, Sp, F.Id("F")),
                    Close, Sp, Rightarrow, RowBreak,
                    Delta, Sp, F.Id("F"), Sp, Le, Sp,
                    Sum, Underscore, Grp(F.Id("i")),
                    F.Id("p"), Open, F.Id("i"), Close, Sp,
                    F.Id("W"), Open, F.Id("i"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p be a nonnegative normalized mass function on a finite type and " +
                        "let W be the work value in each outcome. The hypothesis is the " +
                        "Jarzynski equality written directly with the free-energy difference, " +
                        "so no partition-function definition is introduced.")),
                    Paragraph(Text(
                        "The proof applies Mathlib's finite weighted Jensen inequality for the " +
                        "convex real exponential. The resulting exponential inequality is " +
                        "reflected to an inequality between its exponents, and positivity of " +
                        "beta reverses the negative scaling to give the mean-work bound.")),
                    Paragraph(Text(
                        "This theorem closes only the implication from the stated Jarzynski " +
                        "equality to the second-law inequality. It does not formalize the " +
                        "atom's separate claims about Crooks fluctuations, Spohn monotonicity, " +
                        "thermodynamic length, or numerical residuals."))),
                DescribeRole.Theorem))));
}
