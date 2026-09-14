using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class IterateExponentialModThreeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2026a396family");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive-index coefficients of OEIS A396803 agree with their indices modulo three.",
        H("The Third-Iterate Exponential Congruence Modulo Three"),
        Blocks(
            Paragraph(Text("Let A be the unique rational formal power series with zero "
                + "constant coefficient satisfying A=X*exp(A composed with A composed with A). "
                + "The exponent contains the third compositional iterate. Write a(n)=n![X^n]A. "
                + "The existing sequence aK(3,n) and series AK(3) in IterateExponentialParity "
                + "satisfy this equation by A_equation, and fixed_unique identifies every "
                + "zero-constant solution with AK(3). Thus a(n)=aK(3,n).")),
            Paragraph(Text("Work with integral exponential-generating coefficients modulo "
                + "three, with composition defined by the integral chain-rule recurrence. "
                + "Put l(n)=n and g=l composed with l composed with l. Substitution "
                + "by X*exp(X) sends f(n) to the sum over j from zero to n of "
                + "binomial(n,j)*f(j)*j^(n-j). Lucas decomposition preserves the subsequence "
                + "at indices 3q and makes the subsequence at indices 3q+1 a binomial "
                + "transform. Two transforms of the constant-one subsequence give 3^q. "
                + "Consequently g(3q)=0 and g(3q+1) is one for q=0 and zero otherwise; "
                + "no condition on g(3q+2) is needed.")),
            Describe.Lean(DescribeId.Create("a396803-mod-three-result"),
                DeclarationHandle.Create("D5/S1/Recurrence/Residue/IterateExponentialModThree.result"),
                H("Hanna's congruence for every positive index"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Colon, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(1), Leq, Sp, F.Id("n"), Implies, Sp,
                    new Formula.Modulo(Call("aK", D(3), F.Id("n")), D(3)), Eq,
                    new Formula.Modulo(F.Id("n"), D(3))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For any g with the two support properties above, "
                    + "let E be the integral composition of the constant-one sequence with g. "
                    + "This is the exponential coefficient transformation. The composition "
                    + "recurrence gives E(3q+1)=E(3q), E(3q+2)=E(3q)+S and "
                    + "E(3q+3)=E(3q+2)+2S, with the same auxiliary sum S. Since 3S=0, "
                    + "induction gives E(3q)=E(3q+1)=1. The coefficient transformation "
                    + "for X*exp(A composed with A composed with A) therefore fixes l: "
                    + "at the remaining indices its leading factor is zero modulo three. "
                    + "Induction through every approximation stage, followed by coefficient "
                    + "stabilization, proves the displayed congruence for all n at least one."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396803-iterate-exponential-mod-three"),
                    ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
