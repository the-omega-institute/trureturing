using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class LeastDigitDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive canonical W digits split uniquely according to their least occupied position.",
        H("Least-Digit Zeckendorf Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-raw-least-digit-decomposition"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Admissibility/LeastDigitDecomposition"
                    + ".canonical_raw_least_digit_decomposition"),
                H("Canonical W digits have a unique three-way least-digit form"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("r"), Neq, D(0), Comma, Esc,
                    F.Id("C"), Open, F.Id("r"), Close, Sp, Rightarrow, Sp,
                    Left, Open,
                    Open, F.Id("r"), Underscore, D(0), Comma,
                    F.Id("r"), Underscore, D(1), Close, Eq,
                    Open, D(0), Comma, D(0), Close, Sp, Land, Sp,
                    Exists, Bang, Sp, F.Id("t"), Neq, D(0), Comma, Esc,
                    F.Id("C"), Open, F.Id("t"), Close, Sp, Land, Sp,
                    F.Id("r"), Eq, SigmaLower, Underscore, D(2),
                    Open, F.Id("t"), Close, Close,
                    Sp, Lor, Sp,
                    Open, F.Id("r"), Underscore, D(0), Comma,
                    F.Id("r"), Underscore, D(1), Close, Eq,
                    Open, D(1), Comma, D(0), Close, Sp, Land, Sp,
                    Exists, Bang, Sp, F.Id("t"), Comma, Esc,
                    F.Id("C"), Open, F.Id("t"), Close, Sp, Land, Sp,
                    F.Id("r"), Eq, F.Id("e"), Underscore, D(0), Plus,
                    SigmaLower, Underscore, D(2), Open, F.Id("t"), Close,
                    Sp, Lor, Sp,
                    Open, F.Id("r"), Underscore, D(0), Comma,
                    F.Id("r"), Underscore, D(1), Close, Eq,
                    Open, D(0), Comma, D(1), Close, Sp, Land, Sp,
                    Exists, Bang, Sp, F.Id("t"), Comma, Esc,
                    F.Id("C"), Open, F.Id("t"), Close, Sp, Land, Sp,
                    F.Id("r"), Eq, F.Id("e"), Underscore, D(1), Plus,
                    SigmaLower, Underscore, D(3), Open, F.Id("t"), Close,
                    Right, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a canonical raw W string, each coefficient is zero or one and "
                        + "adjacent occupied positions are forbidden. The first two coefficients "
                        + "therefore have exactly the patterns 00, 10, or 01. These are the three "
                        + "branches selected by the theorem.")),
                    Paragraph(Text(
                        "The operation shiftDigits is the raw-digit realization of sigma: it "
                        + "moves every occupied index upward by a fixed offset. The inverse tail "
                        + "is constructed with Finsupp.comapDomain. Finite support and zero low "
                        + "coefficients let Finsupp.mapDomain_comapDomain recover the original "
                        + "string, while injectivity of index addition gives uniqueness.")),
                    Paragraph(Text(
                        "Pinned Mathlib and D5 were searched before proving. Mathlib provides the "
                        + "Zeckendorf representation and its uniqueness, and D5 already bridges "
                        + "that representation to CanonicalRaw. Neither contains this least-digit "
                        + "three-way decomposition, so the proof combines those checked parts.")),
                    Paragraph(Text(
                        "This closes only the three-way decomposition lemma in part one of source "
                        + "remark 27.158. The beta homogeneity claim, the renormalization equation, "
                        + "its numerical checks, and the diagnostic conclusions are not asserted."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Digit/Raw")),
        ]));
}
