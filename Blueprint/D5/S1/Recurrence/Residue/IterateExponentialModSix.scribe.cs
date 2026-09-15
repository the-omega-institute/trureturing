using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class IterateExponentialModSixDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2026a396806");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive-index coefficients of OEIS A396806 agree with their indices modulo six.",
        H("The Sixth-Iterate Exponential Congruence Modulo Six"),
        Blocks(
            Paragraph(Text("Let A be the unique rational formal power series with zero "
                + "constant coefficient satisfying A=X*exp(A^{[6]}), where A^{[6]} "
                + "denotes the sixth compositional iterate. Write a(n)=n![X^n]A. "
                + "The existing A_equation and fixed_unique in IterateExponentialParity "
                + "identify A with AK(6) and a(n) with its natural sequence aK(6,n).")),
            Describe.Lean(DescribeId.Create("a396806-mod-six-result"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/Residue/IterateExponentialModSix.result"),
                H("Hanna's congruence for every positive index"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Colon, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(1), Leq, Sp, F.Id("n"), Implies, Sp,
                    new Formula.Modulo(Call("aK", D(6), F.Id("n")), D(6)), Eq,
                    new Formula.Modulo(F.Id("n"), D(6))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The conclusion is the pattern 1, 2, 3, 4, 5, 0 "
                        + "repeating modulo six from index one. Since three divides "
                        + "six, it also gives the entry's modulo-three pattern 1, 2, 0.")),
                    Paragraph(Text("Work with integral exponential coefficients modulo "
                        + "three and put l(n)=n. Composition on the right by l acts as "
                        + "the binomial transform T(f)(n)=sum_j binomial(n,j)f(j)j^(n-j). "
                        + "After j transforms, the coefficient at 3q is zero and that "
                        + "at 3q+1 is (j+1)^q. Hence the sixth compositional iterate "
                        + "has zero coefficients at 3q, and at 3q+1 has value one "
                        + "when q=0 and zero otherwise. Its coefficients at 3q+2 "
                        + "need not vanish.")),
                    Paragraph(Text("For any inner sequence with these support properties, "
                        + "the outer exponential has coefficient one at both 3q and "
                        + "3q+1. Its recurrence over three consecutive indices cancels "
                        + "the unrestricted residue-two terms in characteristic three. "
                        + "The leading index factor therefore makes the defining "
                        + "operator preserve l modulo three. Induction through the "
                        + "stabilizing approximations gives the congruence for aK(6,n). "
                        + "The existing modulo-two congruence and coprimality of two "
                        + "and three then give the stated modulo-six conclusion."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396806-iterate-exponential-mod-six"),
                    ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
