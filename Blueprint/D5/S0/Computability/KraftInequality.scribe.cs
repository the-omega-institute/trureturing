using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class KraftInequalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite uniquely decodable binary code has Kraft sum at most one.",
        H("Finite Binary Kraft Inequality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-binary-kraft-inequality"),
                DeclarationHandle.Create("D5/S0/Computability/KraftInequality.finite_binary_kraft_inequality"),
                H("Finite binary Kraft inequality"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("S"), Comma, Sp,
                    F.Id("uniquelyDecodable"), Open, F.Id("S"), Close,
                    Sp, Rightarrow, Sp, F.Id("kraftSum"), Open, F.Id("S"), Close,
                    Sp, Le, Sp, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This is the finite-code partial closure of the source's fixed-input "
                        + "prefix-free coding fact. Pinned mathlib's "
                        + "InformationTheory.kraft_mcmillan_inequality supplies the counting "
                        + "argument, so the Lean declaration is a thin wrapper and does not "
                        + "reprove Kraft-McMillan.")),
                    Paragraph(Text(
                        "The source also discusses an infinite halting set and the bridge from "
                        + "prefix freedom to unique decodability. Those stronger steps are "
                        + "outside this deposited partial closure."))),
                DescribeRole.Theorem))));
}
