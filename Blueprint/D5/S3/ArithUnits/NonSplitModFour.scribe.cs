using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class NonSplitModFourDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The additive quotient from ZMod 4 to ZMod 2 has no additive section.",
        H("A Non-Split Quotient of Finite Cyclic Groups"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-mod-four-quotient-has-no-additive-section"),
                DeclarationHandle.Create(
                    "D5/S3/ArithUnits/NonSplitModFour.mod_four_quotient_has_no_additive_section"),
                H("The mod-four quotient has no additive section"),
                StatementSource.FromAuthor(Disp(Seq(
                    Neg, Sp, Exists, Sp, F.Id("s"), Colon, Sp,
                    Operatorname, Grp(F.Id("AddHom")), Open,
                    Operatorname, Grp(F.Id("ZMod")), Open, D(2), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("ZMod")), Open, D(4), Close, Close, Comma, Esc,
                    F.Id("q"), Sp, Circ, Sp, F.Id("s"), Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("id"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let q be the canonical additive quotient map from ZMod 4 to ZMod 2. "
                        + "There is no additive homomorphism s from ZMod 2 to ZMod 4 for which "
                        + "q composed with s is the identity. Equivalently, this quotient of "
                        + "finite cyclic additive groups does not split.")),
                    Paragraph(Text(
                        "If such a section existed, additivity would force twice s(1) to vanish "
                        + "because twice 1 already vanishes in ZMod 2. Every element of ZMod 4 "
                        + "annihilated by two reduces to zero in ZMod 2, whereas the right-inverse "
                        + "law requires the reduction of s(1) to be one. These conclusions "
                        + "contradict each other.")),
                    Paragraph(Text(
                        "This deposit closes only the nonsplitting ZMod 4 quotient clause of "
                        + "residual appendix E.136. It does not assert the surrounding projection, "
                        + "quantum-extension, Stinespring, entropy-tax, or duality claims from the "
                        + "same source atom.")),
                    Paragraph(Text(
                        "Repository searches found no D5 declaration with this statement. Pinned "
                        + "Mathlib and the local smart-search script supplied ZMod.castHom and "
                        + "ZMod.lift, but no complete nonsplitting theorem. The configured GitHub "
                        + "API credential was expired, and its code-search request returned API key "
                        + "is failed; this failed request is not counted as a no-hit search. A "
                        + "NyxID-proxied Tavily search over GitHub, Loogle, and LeanSearch indexes "
                        + "found the quotient-map infrastructure but no exact theorem. The Lean "
                        + "proof therefore uses Mathlib's canonical quotient map and checks only "
                        + "the finite two-torsion implication locally."))),
                DescribeRole.Theorem))));
}
