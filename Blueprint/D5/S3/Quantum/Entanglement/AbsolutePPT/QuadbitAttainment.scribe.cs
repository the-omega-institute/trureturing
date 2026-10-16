using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class QuadbitAttainmentDocument : IScribeDocumentDefinition
{
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(F.Id(name), [.. xs]);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, F.Eq, b);
    private static Formula And(params Formula[] xs) => Seq(xs.SelectMany((f, i) => i == 0
        ? new[] { f } : new[] { Land, Sp, f }).ToArray());
    public DocumentDefinition Create()
    {
        var rho = F.Id("rho");
        var tr = Call("Matrix.trace", rho);
        var square = Seq(rho, Cdot, Sp, rho);
        var statement = And(Call("APPT", rho), Call("Matrix.PosSemidef", rho),
            Eqn(tr, Num(1)), Eqn(Call("Complex.re", Call("Matrix.trace", square)),
                new Formula.Fraction(Num(2), Num(27))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "An explicit density matrix on Fin 4 × Fin 4 is absolutely PPT and has purity 2/27.",
            H("Quadbit APPT attainment"), Blocks(
                Describe.Lean(DescribeId.Create("appt-quadbit-attainment"),
                    DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitAttainment.attainment"),
                    H("Explicit 4 by 4 lower-bound witness"), StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                        "Here rho is the explicit matrix (I + 2 |e00><e00|)/18 on Fin 4 × Fin 4. Its spectrum is 1/6 followed by fifteen copies of 1/18. The proof reuses the separable-cone rank-one ray theorem after each global unitary conjugation and proves that partial transpose preserves positivity of every separable-cone element. This establishes attainment and hence the purity lower bound 2/27. It proves no global upper bound and does not settle the maximum-purity problem."))),
                    DescribeRole.Theorem))));
    }
}
