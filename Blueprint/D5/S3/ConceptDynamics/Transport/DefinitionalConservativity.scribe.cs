using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Transport;

internal sealed class DefinitionalConservativityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Definitional extensions obtained by expanding every axiom and rule are conservative on the old language.",
        H("Definitional Conservativity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("definitional-conservativity"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Transport/DefinitionalConservativity."
                        + "definitional_conservativity"),
                H("Definitional conservativity"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A calculus consists of an axiom predicate and a rule predicate on "
                            + "finite lists of premises. The extension calculus is constructed "
                            + "by applying the source expansion map to every axiom, premise, and "
                            + "conclusion; it introduces no independent axiom or rule.")),
                    Paragraph(Text(
                        "The old-language embedding is required to be a section of expansion. "
                            + "Induction on an extended derivation then yields a base derivation "
                            + "of the expanded conclusion, and the section law identifies that "
                            + "conclusion with the original old-language sentence.")),
                    Paragraph(Text(
                        "This is the source's definitional-extension conservativity clause: every "
                            + "old-language sentence derivable in the expansion-only calculus was "
                            + "already derivable in the base calculus."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
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
        Formula baseLanguage = F.Id("B");
        Formula extendedLanguage = F.Id("E");
        Formula baseCalculus = F.Id("C");
        Formula expansion = F.Id("e");
        Formula embedding = F.Id("i");
        Formula sentence = F.Id("phi");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula extension = Call("pullbackCalculus", baseCalculus, expansion);
        Formula derivation = Call("Derivation", extension, Call("i", sentence));
        Formula baseDerivation = Call("Derivation", baseCalculus, sentence);
        Formula sectionLaw = Grp(Open,
            Forall, Sp, sentence, Colon, Sp, baseLanguage, Comma, Sp,
            expansion, Open, embedding, Open, sentence, Close, Close,
            Sp, Eq, Sp, sentence, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, baseLanguage, Comma, Sp, extendedLanguage, Colon, Sp, type,
            Comma, Sp, RowBreak, Grp(),
            baseCalculus, Colon, Sp, Call("Calculus", baseLanguage), Comma, Sp,
            expansion, Colon, Sp, extendedLanguage, Sp, To, Sp, baseLanguage, Comma, Sp,
            embedding, Colon, Sp, baseLanguage, Sp, To, Sp, extendedLanguage, Comma,
            RowBreak, Grp(),
            sectionLaw, Comma, RowBreak, Grp(),
            sentence, Colon, Sp, baseLanguage, Comma, RowBreak, Grp(),
            Open, derivation, Close, Sp, Rightarrow, Sp, baseDerivation, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
