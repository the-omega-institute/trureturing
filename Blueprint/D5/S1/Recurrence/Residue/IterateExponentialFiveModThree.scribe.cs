using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class IterateExponentialFiveModThreeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2026a396805");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "From index three, the coefficients of OEIS A396805 have repeating residues 0, 1, 0 modulo three.",
        H("The Fifth-Iterate Exponential Pattern Modulo Three"),
        Blocks(
            Paragraph(Text("Let A be the unique rational formal series with zero "
                + "constant coefficient satisfying A=X*exp(A^{[5]}), where A^{[5]} "
                + "is the fifth compositional iterate. Write a(n)=n![X^n]A. The "
                + "existing A_equation and fixed_unique in IterateExponentialParity "
                + "identify A with AK(5) and a(n) with aK(5,n). In the formula, "
                + "ite(p,x,y) equals x when p holds and y otherwise.")),
            Describe.Lean(DescribeId.Create("a396805-mod-three-result"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/Residue/IterateExponentialFiveModThree.result"),
                H("Hanna's pattern from index three"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Colon, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(3), Leq, Sp, F.Id("n"), Implies, Sp,
                    new Formula.Modulo(Call("aK", D(5), F.Id("n")), D(3)), Eq,
                    Call("ite", Seq(new Formula.Modulo(F.Id("n"), D(3)), Eq, D(1)),
                        D(1), D(0))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The residue is one precisely at indices "
                    + "congruent to one modulo three and zero at the other indices "
                    + "in the domain n>=3. This is the source pattern 0, 1, 0 starting "
                    + "at n=3. The source value a(2)=2 explains why that lower bound "
                    + "must be retained. The earlier parity result and the separately "
                    + "recorded non-kernel modulo-five counterexamples have their "
                    + "own evidence; this theorem resolves only the modulo-three clause."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396805-iterate-exponential-mod-three"),
                    ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
