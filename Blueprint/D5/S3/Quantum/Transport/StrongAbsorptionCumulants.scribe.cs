using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Transport;

internal sealed class StrongAbsorptionCumulantsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "StrongAbsorptionCumulants for the strong-absorption cumulant expansion.",
        H("StrongAbsorptionCumulants"),
        Blocks(
            Paragraph(Text("Natural-number subtraction is truncated. Unmarked integrals use volume; real-number powers and division use the real field.")),
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorptionCumulants.claim"),
                H("claim"), StatementSource.FromAuthor(Disp(Seq(V("claim"), Sp, Eq, Sp, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Note()),
                Blocks(Paragraph(Text("Novaes, Section 5, p. 7: “we conjecture that, for n > 1,” followed by Eq. (58). Natural n ≥ 2 expresses n > 1. The two coefficients and the absolute remainder bound refer to every M ≥ 1. The constants may depend on M and n."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorptionCumulants.result"),
                H("result"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Note()),
                Blocks(Paragraph(Text("For every positive channel number and every cumulant order at least two, the normalized law has the two strong-absorption coefficients of Novaes, Eq. (58)."))), DescribeRole.Theorem)
        )));

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static LibraryNoteRef Note() => LibraryNoteRef.Create("D5/L/StatisticalMechanics/novaes2023absorption");

    private static Formula ClaimBody() =>
        Seq(Forall, Sp, V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))), Sp, Comma, Sp, D(1), Sp, Le, Sp, V("M"), Sp, To, Sp, Forall, Sp, V("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))), Sp, Comma, Sp, D(2), Sp, Le, Sp, V("n"), Sp, To, Sp, Exists, Sp, V("C"), Sp, new Formula.Subscript(GammaLower, D(0)), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, Comma, Sp, D(0), Sp, Lt, Sp, new Formula.Subscript(GammaLower, D(0)), Sp, Land, Sp, Forall, Sp, GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, Comma, Sp, new Formula.Subscript(GammaLower, D(0)), Sp, Le, Sp, GammaLower, Sp, To, Sp, Bar, Sp, Sp, new Formula.Power(Parenthesized(Seq(Minus, Sp, D(1), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), V("n")), Sp, Cdot, Sp, V("kappa"), Sp, V("M"), Sp, V("n"), Sp, GammaLower, Sp, Minus, Sp, Parenthesized(Seq(Parenthesized(Seq(V("n"), Sp, Minus, Sp, D(1))), Sp, Dot, Sp, V("factorial"), Sp, Slash, Sp, Parenthesized(Seq(new Formula.Power(Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Seq(D(2), Sp, Cdot, Sp, V("n"), Sp, Minus, Sp, D(2))), Sp, Cdot, Sp, Sp, new Formula.Power(GammaLower, Seq(D(2), Sp, Cdot, Sp, V("n"))))), Sp, Minus, Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, V("n"), Sp, Minus, Sp, D(1))), Sp, Cdot, Sp, V("n"), Sp, Cdot, Sp, Parenthesized(Seq(V("n"), Sp, Minus, Sp, D(1))), Sp, Dot, Sp, V("factorial"), Sp, Slash, Sp, Parenthesized(Seq(new Formula.Power(Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Seq(D(2), Sp, Cdot, Sp, V("n"), Sp, Minus, Sp, D(2))), Sp, Cdot, Sp, Sp, new Formula.Power(GammaLower, Seq(D(2), Sp, Cdot, Sp, V("n"), Sp, Plus, Sp, D(1))))))), Sp, Bar, Sp, Le, Sp, V("C"), Sp, Slash, Sp, Sp, new Formula.Power(GammaLower, Seq(D(2), Sp, Cdot, Sp, V("n"), Sp, Plus, Sp, D(2))));
}
