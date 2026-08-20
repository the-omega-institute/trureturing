using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumStates;

internal sealed class GNSZeroPropagationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive normalized matrix trace functional propagates a zero quadratic value to every mixed value.",
        H("Zero Norm Propagation for Matrix States"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-matrix-functional-zero-norm-propagation"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumStates/GNSZeroPropagation."
                        + "gns_zero_norm_propagation"),
                H("A zero quadratic value annihilates every mixed value"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("d"), Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, F.Id("d"), Close,
                    CloseBracket, Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("DecidableEq")), Open, F.Id("d"), Close,
                    CloseBracket, Comma, Esc,
                    Forall, Sp, Rho, Comma, Sp, F.Id("g"), Sp, InMacro, Sp,
                    Call("Matrix", F.Id("d"), F.Id("d"), Mathbb, Grp(F.Id("C"))), Comma, Esc,
                    Call("PosSemidef", Rho), Sp, Land, Sp,
                    Call("trace", Rho), Sp, Eq, Sp, D(1), Sp, Land, Sp,
                    Call("stateFunctional", Rho,
                        Seq(F.Id("g"), Caret, Grp(Star), Sp, F.Id("g"))), Sp, Eq, Sp, D(0),
                    Sp, Rightarrow, Sp,
                    Forall, Sp, F.Id("h"), Sp, InMacro, Sp,
                    Call("Matrix", F.Id("d"), F.Id("d"), Mathbb, Grp(F.Id("C"))), Comma, Esc,
                    Call("stateFunctional", Rho,
                        Seq(F.Id("h"), Caret, Grp(Star), Sp, F.Id("g"))), Sp, Eq, Sp, D(0), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state functional is the source trace pairing Tr(rho times a), with rho positive semidefinite and trace one. Its quadratic value at g is the squared Frobenius norm of g times the positive square root of rho.")),
                    Paragraph(Text(
                        "A zero quadratic value therefore makes g times the square root of rho equal to zero. The same factorization for an arbitrary h proves the mixed trace value Tr(rho h star g) is zero.")),
                    Paragraph(Text(
                        "The matrix GNS identity is reused directly; the deposited statement retains positivity, normalization, and the universal mixed-value conclusion as public clauses."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
