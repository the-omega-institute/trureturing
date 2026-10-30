using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;
internal sealed class QubitEntropyContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic contraction for an actual symmetric qubit ensemble", H("QubitEntropyContraction"), Blocks(
            Describe.Lean(DescribeId.Create("holevo-contraction"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/QubitEntropyContraction.qubit_holevo_contraction"),
                H("Quadratic contraction for an actual symmetric qubit ensemble"), StatementSource.FromAuthor(Seq(Forall, Sp, Seq(F.Id("x"), Comma, F.Id("z"), Comma, F.Id("t")), Colon, Seq(Mathbb, Grp(F.Id("R"))), Comma, Esc, Seq(Grp(Seq(Seq(Seq(Seq(Open, Seq(F.Id("x"), Caret, Grp(D(2))), Close), Plus, Seq(Open, Seq(F.Id("z"), Caret, Grp(D(2))), Close)), Le, D(1)), Land, Seq(D(0), Le, F.Id("t")), Land, Seq(F.Id("t"), Le, D(1)))), Implies, Seq(Seq(D(0), Le, Call("qubitHolevo", F.Id("x"), Seq(Seq(Open, F.Id("t"), Close), Times, Seq(Open, F.Id("z"), Close)))), Land, Seq(Call("qubitHolevo", F.Id("x"), Seq(Seq(Open, F.Id("t"), Close), Times, Seq(Open, F.Id("z"), Close))), Le, Seq(Seq(Open, Seq(F.Id("t"), Caret, Grp(D(2))), Close), Times, Seq(Open, Call("qubitHolevo", F.Id("x"), F.Id("z")), Close))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("For every point of the closed qubit disk and every t in [0,1], the symmetric binary Holevo entropy is nonnegative and contracts by at most t squared when z is replaced by tz. The proof derives concavity of u mapped to binary entropy of (1+sqrt(u))/2 from scalar derivatives on (0,1), with continuity at both endpoints. The matrix statement then uses the actual qubit density states and their spectral entropy, including pure, zero-separation and maximal-mixing cases."))), DescribeRole.Theorem))));

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
