using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;
internal sealed class FinitePreparationChannelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite density-state preparation as an actual quantum channel", H("FinitePreparationChannel"), Blocks(
            Describe.Lean(DescribeId.Create("finite-preparation"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FinitePreparationChannel.finite_preparation_quantum_channel"),
                H("Finite density-state preparation as an actual quantum channel"), StatementSource.FromAuthor(Seq(Forall, Sp, Seq(F.Id("u")), Colon, Call("Level"), Comma, Esc, Seq(Forall, Sp, Seq(F.Id("v")), Colon, Call("Level"), Comma, Esc, Seq(Forall, Sp, Seq(F.Id("a")), Colon, Call("Type", F.Id("u")), Comma, Esc, Seq(Grp(Seq(Call("Fintype", F.Id("a")), Land, Sp, Call("DecidableEq", F.Id("a")))), Implies, Sp, Seq(Forall, Sp, Seq(F.Id("b")), Colon, Call("Type", F.Id("v")), Comma, Esc, Seq(Grp(Seq(Call("Fintype", F.Id("b")), Land, Sp, Call("DecidableEq", F.Id("b")))), Implies, Sp, Seq(Forall, Sp, Seq(F.Id("rho")), Colon, Seq(F.Id("a"), Rightarrow, Sp, Call("DensityState", F.Id("b"))), Comma, Esc, Seq(Exists, Sp, F.Id("Phi"), Colon, Call("QuantumChannel", F.Id("a"), F.Id("b")), Comma, Esc, Seq(Forall, Sp, Seq(F.Id("X")), Colon, Call("Matrix", F.Id("a"), F.Id("a"), Seq(Mathbb, Grp(F.Id("C")))), Comma, Esc, Seq(Call("raw", Call("apply", F.Id("Phi"), F.Id("X"))), Eq, Seq(Sum, Sp, Underscore, Grp(F.Id("i")), Seq(Seq(Open, Call("entry", F.Id("X"), F.Id("i"), F.Id("i")), Close), Times, Sp, Seq(Open, Call("raw", Call("apply", F.Id("rho"), F.Id("i"))), Close)))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("For an arbitrary finite family of actual density matrices, there exists a canonical CPTP map whose action on every complex input matrix X is the sum of its diagonal entries Xii times the respective density matrices. The construction uses columns of each positive square root as Kraus operators. The normalization follows from the actual trace-one condition, including singular outputs, and the full-algebra action is proved from the same Kraus family. For x in [0,1], take the two prepared qubits (I+xX plus or minus sqrt(1-x squared)Z)/2. On the diagonal input (I+tZ)/2, the formula gives (I+xX+t sqrt(1-x squared)Z)/2 for every real t. For t in [-1,1], these inputs and outputs are density states. This physical preparation operation asserts no entropy inequality by itself."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("local-preparation"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FinitePreparationChannel.finite_local_preparation_quantum_channel"),
                H("Local preparation with an arbitrary quantum spectator"), StatementSource.FromAuthor(Seq(Forall, Sp, Seq(F.Id("u")), Colon, Call("Level"), Comma, Esc, Seq(Forall, Sp, Seq(F.Id("v")), Colon, Call("Level"), Comma, Esc, Seq(Forall, Sp, Seq(F.Id("w")), Colon, Call("Level"), Comma, Esc, Seq(Forall, Sp, Seq(F.Id("a")), Colon, Call("Type", F.Id("u")), Comma, Esc, Seq(Grp(Seq(Call("Fintype", F.Id("a")), Land, Sp, Call("DecidableEq", F.Id("a")))), Implies, Sp, Seq(Forall, Sp, Seq(F.Id("b")), Colon, Call("Type", F.Id("v")), Comma, Esc, Seq(Grp(Seq(Call("Fintype", F.Id("b")), Land, Sp, Call("DecidableEq", F.Id("b")))), Implies, Sp, Seq(Forall, Sp, Seq(F.Id("s")), Colon, Call("Type", F.Id("w")), Comma, Esc, Seq(Grp(Seq(Call("Fintype", F.Id("s")), Land, Sp, Call("DecidableEq", F.Id("s")))), Implies, Sp, Seq(Forall, Sp, Seq(F.Id("rho")), Colon, Seq(F.Id("a"), Rightarrow, Sp, Call("DensityState", F.Id("b"))), Comma, Esc, Seq(Exists, Sp, F.Id("Phi"), Colon, Call("QuantumChannel", Call("Prod", F.Id("s"), F.Id("a")), Call("Prod", F.Id("s"), F.Id("b"))), Comma, Esc, Seq(Forall, Sp, Seq(F.Id("X")), Colon, Call("Matrix", Call("Prod", F.Id("s"), F.Id("a")), Call("Prod", F.Id("s"), F.Id("a")), Seq(Mathbb, Grp(F.Id("C")))), Comma, Esc, Seq(Forall, Sp, Seq(F.Id("r"), Comma, F.Id("t")), Colon, Call("Prod", F.Id("s"), F.Id("b")), Comma, Esc, Seq(Call("entry", Call("raw", Call("apply", F.Id("Phi"), F.Id("X"))), F.Id("r"), F.Id("t")), Eq, Seq(Sum, Sp, Underscore, Grp(F.Id("i")), Seq(Seq(Open, Call("entry", F.Id("X"), Call("pair", Call("fst", F.Id("r")), F.Id("i")), Call("pair", Call("fst", F.Id("t")), F.Id("i"))), Close), Times, Sp, Seq(Open, Call("entry", Call("raw", Call("apply", F.Id("rho"), F.Id("i"))), Call("snd", F.Id("r")), Call("snd", F.Id("t"))), Close)))))))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("Tensoring each preparation Kraus operator with the spectator identity gives an actual CPTP map on the joint matrix algebra. Its matrix entries are the sum over the measured input index of the original spectator block entry times the prepared density entry. Thus every off-diagonal spectator coherence is preserved. The spectator, input and output dimensions are arbitrary finite types, and prepared states may be singular. This is the physical local operation needed before applying canonical relative-entropy data processing; it assumes no mutual-information inequality."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
