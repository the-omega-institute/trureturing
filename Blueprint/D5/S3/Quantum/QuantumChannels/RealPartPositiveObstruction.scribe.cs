using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class RealPartPositiveObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On a finite complex matrix algebra, transpose symmetrization is the complex-linear map X to one half of X plus its transpose. It is positive and preserves trace. On Hermitian inputs its entries are the real parts of the input entries. Every symmetric trace readout is preserved.",
        H("Real Readouts and Complete Positivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("realpartpositiveobstruction"),
                DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/RealPartPositiveObstruction.real_part_readout_obstruction"),
                H("Real Readouts and Complete Positivity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Colon, F.Id("Type"), Comma,
                    OpenBracket, C("Fintype", F.Id("n")), CloseBracket,
                    OpenBracket, C("DecidableEq", F.Id("n")), CloseBracket, Comma,
                    Forall, Sp, F.Id("a"), Comma, F.Id("b"), Colon, F.Id("n"), Comma, F.Id("a"), Neq, Sp, F.Id("b"),
                    Rightarrow, Sp, C("Positive", C("symmetrize", F.Id("n"))), Land, Sp, C("TracePreserving", C("symmetrize", F.Id("n"))), Land, Sp,
                    Open, Forall, Sp, F.Id("X"), Colon, C("ComplexMatrix", F.Id("n")), Comma, C("Hermitian", F.Id("X")), Rightarrow, Sp,
                    Forall, Sp, F.Id("i"), Comma, F.Id("j"), Colon, F.Id("n"), Comma,
                    C("entry", C("symmetrize", F.Id("X")), F.Id("i"), F.Id("j")), Eq,
                    C("Re", C("X", F.Id("i"), F.Id("j"))), Close, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("E"), Comma, F.Id("X"), Colon, C("ComplexMatrix", F.Id("n")), Comma,
                    C("transpose", F.Id("E")), Eq, F.Id("E"), Rightarrow, Sp,
                    C("Tr", Seq(F.Id("E"), C("symmetrize", F.Id("X")))), Eq,
                    C("Tr", Seq(F.Id("E"), F.Id("X"))), Close, Land, Sp, RowBreak,
                    C("Choi", C("symmetrize", F.Id("n"))), C("antisymmetric", F.Id("a"), F.Id("b")), Eq,
                    Minus, Frac, Grp(D(1)), Grp(D(2)), C("antisymmetric", F.Id("a"), F.Id("b")), Land, Sp,
                    Frac, Grp(C("Choi", C("symmetrize", F.Id("n")))), Grp(C("card", F.Id("n"))), C("antisymmetric", F.Id("a"), F.Id("b")), Eq,
                    Minus, Frac, Grp(D(1)), Grp(Seq(D(2), C("card", F.Id("n")))), C("antisymmetric", F.Id("a"), F.Id("b")), Land, Sp,
                    Neg, Sp, C("CP", C("symmetrize", F.Id("n")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("On a finite complex matrix algebra, transpose symmetrization is the complex-linear map X to one half of X plus its transpose. It is positive and preserves trace. On Hermitian inputs its entries are the real parts of the input entries. Every symmetric trace readout is preserved.")),
                    Paragraph(Text("For two distinct basis indices a and b, the antisymmetric tensor e_a tensor e_b minus e_b tensor e_a is an eigenvector of the actual unnormalized Choi matrix with eigenvalue minus one half. Its quadratic value is minus one, so the Choi matrix is not positive semidefinite. The finite Kraus and Choi equivalence therefore excludes complete positivity.")),
                    Paragraph(Text("The normalized Choi eigenvalue in dimension d is minus one over two d. Statistical preservation by a positive map does not supply a quantum channel valid on arbitrary ancillary extensions. Measurement-relative compression is studied by Bluhm, Rauber and Wolf, arXiv:1708.04898v4; Koashi and Imoto, quant-ph/0101144, provide broader no-disturbance structure. No novelty or optimality claim is made."))),
                DescribeRole.Theorem))));

    private static Formula C(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
