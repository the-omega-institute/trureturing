using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class MarkovEquationMutationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A coordinate mutation preserves the defining cubic equation.",
        H("Coordinate Mutation of the Cubic Equation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coordinate-mutation-preserves-the-cubic-equation"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/MarkovEquationMutation.markov_equation_mutation"),
                H("The coordinate mutation preserves the equation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("R"), Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("CommRing")), Open, F.Id("R"), Close,
                    CloseBracket, Comma, Esc,
                    Forall, Sp, F.Id("x"), Comma, F.Id("y"), Comma, F.Id("z"), InMacro, Sp,
                    F.Id("R"), Comma, Esc,
                    F.Id("x"), Caret, Grp(D(2)), Plus,
                    F.Id("y"), Caret, Grp(D(2)), Plus,
                    F.Id("z"), Caret, Grp(D(2)), Eq,
                    D(3), F.Id("x"), F.Id("y"), F.Id("z"), Sp, Rightarrow, Sp,
                    F.Id("x"), Caret, Grp(D(2)), Plus,
                    F.Id("y"), Caret, Grp(D(2)), Plus,
                    Open, D(3), F.Id("x"), F.Id("y"), Minus, F.Id("z"), Close,
                    Caret, Grp(D(2)), Eq,
                    D(3), F.Id("x"), F.Id("y"),
                    Open, D(3), F.Id("x"), F.Id("y"), Minus, F.Id("z"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source displays the equation x^2 + y^2 + z^2 = 3xyz and says its "
                        + "integer solutions form a tree. This partial closure isolates the standard "
                        + "edge operation: replace z by 3xy - z while leaving x and y fixed. The "
                        + "conclusion states that the resulting triple satisfies the same equation.")),
                    Paragraph(Text(
                        "Expansion of the new square introduces 9x^2y^2 - 6xyz. Substituting the "
                        + "original equation and collecting terms gives 3xy(3xy - z). Because this "
                        + "calculation uses only commutative-ring identities, the declaration is "
                        + "freely generalized beyond the intended integer specialization.")),
                    Paragraph(Text(
                        "This deposit does not prove independence of the real quadratic fields, "
                        + "classify or enumerate the full solution tree, identify the complete "
                        + "worst-approximable spectrum, or establish the source's extremality and "
                        + "branch-position claims. Those subitems remain unresolved."))),
                DescribeRole.Theorem)),
        []));
}
