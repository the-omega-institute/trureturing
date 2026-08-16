using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.EscapeProbability;

internal sealed class ZeroCharacterizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero escape probability occurs exactly for identity twists in the two finite "
            + "degeneracies.",
        H("Zero Escape-Probability Characterization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-escape-probability-characterization"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/EscapeProbability/ZeroCharacterization."
                        + "escape_probability_eq_zero_iff"),
                H("Identity twists characterize zero escape probability"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Y"), Comma, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, F.Id("Y"),
                    CloseBracket, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Nonempty")), Sp, F.Id("Y"),
                    CloseBracket, Comma, Sp,
                    Forall, Sp, F.Id("f"), Colon, Sp, F.Id("Y"), Sp, To, Sp, F.Id("Y"),
                    Comma, Sp, Forall, Sp, F.Id("A"), Colon, Sp, Mathbb, Grp(F.Id("N")),
                    Comma, Sp,
                    Call("escapeProbability", Call("Fin", F.Id("A")), F.Id("f")),
                    Sp, Eq, Sp, D(0), Sp, Iff, Sp,
                    D(0), Sp, Lt, Sp, F.Id("A"), Sp, Land, Sp,
                    F.Id("f"), Sp, Eq, Sp, Operatorname, Grp(F.Id("id")), Sp, Land, Sp,
                    Open, F.Id("A"), Sp, Eq, Sp, D(1), Sp, Lor, Sp,
                    Call("card", F.Id("Y")), Sp, Eq, Sp, D(1), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite nonempty output alphabet Y, an endomorphism f, and A "
                            + "addresses, the frozen escape probability is zero exactly when A "
                            + "is positive, f is the identity, and either A=1 or Y is a "
                            + "singleton.")),
                    Paragraph(Text(
                        "The frozen closed form reduces vanishing to equality between the "
                            + "fixed-point count and card(Y)^A. The fixed-point subtype bound "
                            + "then forces every output to be fixed. Injectivity of natural "
                            + "powers for card(Y) at least two leaves exponent one; the only "
                            + "alternative is the singleton alphabet.")),
                    Paragraph(Text(
                        "This complements the probability-one endpoint without restating any "
                            + "frozen theorem. Both degeneracies are necessary: one address "
                            + "works for every identity twist, while a singleton alphabet works "
                            + "for every positive address count."))),
                DescribeRole.Theorem)),
        []));
}
