using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class CassiniFrickeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The Cassini-Fricke quadratic form is an alternating invariant of Binet recurrences.",
H("Cassini-Fricke Antiinvariant"),
Blocks(
            Describe.Lean(
                DescribeId.Create("cassini-fricke-quadratic-form-antiinvariant"),
                DeclarationHandle.Create("D5/S1/Recurrence/CassiniFricke.cassini_fricke"),
                H("Cassini-Fricke quadratic-form antiinvariant"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Q"), Open, F.Id("u"), Underscore,
                    Grp(F.Id("K"), Plus, D(1)), Comma, Sp,
                    F.Id("u"), Underscore, F.Id("K"), Close, Eq,
                    F.Id("u"), Underscore, Grp(F.Id("K"), Plus, D(1)),
                    Caret, Grp(D(2)), Minus,
                    F.Id("u"), Underscore, Grp(F.Id("K"), Plus, D(1)),
                    F.Id("u"), Underscore, F.Id("K"), Minus,
                    F.Id("u"), Underscore, F.Id("K"), Caret, Grp(D(2)), Eq,
                    Minus, D(5), F.Id("A"), F.Id("B"),
                    Open, Minus, D(1), Close, Caret, Grp(F.Id("K"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let phi and psi satisfy phi^2 = phi + 1, psi^2 = psi + 1, "
                    + "phi + psi = 1, and phi*psi = -1 in a commutative ring. For the "
                    + "Binet sequence u_K = A*phi^K + B*psi^K and the quadratic form "
                    + "Q(a,b) = a^2 - a*b - b^2, the value Q(u_(K+1),u_K) is "
                    + "-5*A*B*(-1)^K. Taking A = -x*phi and B = y*psi gives A*B = x*y, "
                    + "so the result is 5*x*y*(-1)^(K+1), exactly the source theorem's "
                    + "Cassini-Fricke antiinvariant."))),
                DescribeRole.Theorem))));
}
