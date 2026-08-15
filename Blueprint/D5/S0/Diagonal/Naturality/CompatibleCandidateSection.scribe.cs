using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Naturality;

internal sealed class CompatibleCandidateSectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonempty finite candidate subsets preserved by a cofiltered diagram admit a compatible section.",
        H("Compatible Sections of Finite Candidate Systems"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cofiltered-finite-candidates-admit-a-compatible-section"),
                DeclarationHandle.Create(
                    "D5/S0/Diagonal/Naturality/CompatibleCandidateSection."
                    + "compatible_candidate_section_nonempty"),
                H("Cofiltered finite candidates admit a compatible section"),
                StatementSource.FromAuthor(CompatibleCandidateSectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let J be a cofiltered category, D a diagram of types indexed by J, and "
                        + "O assign a candidate subset of D(i) to every object i. Assume every "
                        + "candidate subtype O(i) is finite and nonempty.")),
                    Paragraph(Text(
                        "Assume each diagram transition from i to j sends every member of O(i) "
                        + "into O(j). The restricted candidate subtypes form their own diagram. "
                        + "A section of that diagram supplies a candidate at every index, proves "
                        + "membership pointwise, and makes all transitions compatible.")),
                    Paragraph(Text(
                        "Pinned Mathlib, Loogle, and LeanSearch all returned "
                        + "nonempty_sections_of_finite_cofiltered_system as the exact general "
                        + "section-existence result. The Lean proof imports and applies that "
                        + "theorem to the restricted candidate diagram; repository searches found "
                        + "no existing declaration of the full candidate-subset statement."))),
                DescribeRole.Theorem)),
        []));

    private static Formula CompatibleCandidateSectionFormula()
    {
        Formula j = F.Id("J");
        Formula d = F.Id("D");
        Formula o = F.Id("O");
        Formula i = F.Id("i");
        Formula k = F.Id("j");
        Formula f = F.Id("f");
        Formula x = F.Id("x");

        return Disp(Seq(
            Forall, Sp, j, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("Category")), Open, j, Close,
            CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("IsCofiltered")), Open, j, Close,
            CloseBracket, Comma, Esc,
            Forall, Sp, d, Colon, Sp,
            Operatorname, Grp(F.Id("Functor")), Open, j, Comma, Sp,
            Operatorname, Grp(F.Id("Type")), Close, Comma, Esc,
            o, Colon, Sp, Forall, Sp, i, Colon, Sp, j, Comma, Sp,
            Operatorname, Grp(F.Id("Set")), Open, d, Open, i, Close, Close, Comma, Esc,
            Open, Forall, Sp, i, Comma, Sp, k, Colon, Sp, j, Comma, Sp,
            f, Colon, Sp, Operatorname, Grp(F.Id("Hom")), Open, i, Comma, Sp, k, Close,
            Comma, Sp, x, Colon, Sp, d, Open, i, Close, Comma, Esc,
            x, Sp, InMacro, Sp, o, Open, i, Close, Sp, Rightarrow, Sp,
            d, Open, f, Close, Open, x, Close, Sp, InMacro, Sp, o, Open, k, Close,
            Close, Sp, Rightarrow, Sp,
            Open, Forall, Sp, i, Colon, Sp, j, Comma, Sp,
            Operatorname, Grp(F.Id("Finite")), Open, o, Open, i, Close, Close,
            Close, Sp, Rightarrow, Sp,
            Open, Forall, Sp, i, Colon, Sp, j, Comma, Sp,
            Operatorname, Grp(F.Id("Nonempty")), Open, o, Open, i, Close, Close,
            Close, Sp, Rightarrow, Sp,
            Operatorname, Grp(F.Id("Nonempty")), Open,
            Operatorname, Grp(F.Id("CandidateSection")), Open, d, Comma, Sp, o, Close,
            Close, Dot));
    }
}
