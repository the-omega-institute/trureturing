using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;
internal sealed class QubitNormalFormStateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual closed-disk qubit entropy", H("QubitNormalFormState"), Blocks(
            Describe.Lean(DescribeId.Create("qubit-entropy"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/QubitNormalFormState.qubit_state_entropy"),
                H("The actual closed-disk qubit entropy"), StatementSource.FromAuthor(Seq(Forall, Sp, Seq(F.Id("x"), Comma, F.Id("z")), Colon, Seq(Mathbb, Grp(F.Id("R"))), Comma, Esc, Seq(Grp(Seq(Seq(Seq(Open, Seq(F.Id("x"), Caret, Grp(D(2))), Close), Plus, Seq(Open, Seq(F.Id("z"), Caret, Grp(D(2))), Close)), Le, Sp, D(1))), Implies, Sp, Seq(Call("S", Call("qubitState", F.Id("x"), F.Id("z"))), Eq, Call("h", Seq(Frac, Grp(Seq(Seq(Open, D(1), Close), Plus, Seq(Open, Seq(Sqrt, Grp(Seq(Seq(Open, Seq(F.Id("x"), Caret, Grp(D(2))), Close), Plus, Seq(Open, Seq(F.Id("z"), Caret, Grp(D(2))), Close)))), Close))), Grp(D(2)))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("The matrix is (I+xX+zZ)/2 in the computational basis, with real x and z and x squared plus z squared at most one. Its constructor proves positivity and trace one, including the pure boundary. The entropy on the left is the canonical CFC von Neumann entropy in natural logarithms. The proof reuses FormationBounds.qubit_entropy_det, cancels its log(2) conversion from bits, and uses the original spectral/CFC bridge."))), DescribeRole.Theorem))));

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
