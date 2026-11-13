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
                H("Quadratic contraction for an actual symmetric qubit ensemble"), StatementSource.FromAuthor(Seq(Forall, Sp, Seq(F.Id("x"), Comma, F.Id("z"), Comma, F.Id("t")), Colon, Seq(Mathbb, Grp(F.Id("R"))), Comma, Esc, Seq(Grp(Seq(Seq(Seq(Seq(Open, Seq(F.Id("x"), Caret, Grp(D(2))), Close), Plus, Seq(Open, Seq(F.Id("z"), Caret, Grp(D(2))), Close)), Le, Sp, D(1)), Land, Sp, Seq(D(0), Le, Sp, F.Id("t")), Land, Sp, Seq(F.Id("t"), Le, Sp, D(1)))), Implies, Sp, Seq(Seq(D(0), Le, Sp, Call("qubitHolevo", F.Id("x"), Seq(Seq(Open, F.Id("t"), Close), Times, Sp, Seq(Open, F.Id("z"), Close)))), Land, Sp, Seq(Call("qubitHolevo", F.Id("x"), Seq(Seq(Open, F.Id("t"), Close), Times, Sp, Seq(Open, F.Id("z"), Close))), Le, Sp, Seq(Seq(Open, Seq(F.Id("t"), Caret, Grp(D(2))), Close), Times, Sp, Seq(Open, Call("qubitHolevo", F.Id("x"), F.Id("z")), Close))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/codex2026productmargin")),
                Blocks(
                    Paragraph(Text("For every point of the closed qubit disk and every t in [0,1], the symmetric binary Holevo entropy is nonnegative and contracts by at most t squared when z is replaced by tz. The proof derives concavity of u mapped to binary entropy of (1+sqrt(u))/2 from scalar derivatives on (0,1), with continuity at both endpoints. The matrix statement then uses the actual qubit density states and their spectral entropy, including pure, zero-separation and maximal-mixing cases.")),
                    Paragraph(Text("An application to three real coordinates uses binary entropy in nats. For p in the closed unit interval, write "),
                        Math(Seq(Call("h", F.Id("p")), Eq, Minus, F.Id("p"), Thin, Call("ln", F.Id("p")), Minus, Open, D(1), Minus, F.Id("p"), Close, Thin, Call("ln", Seq(D(1), Minus, F.Id("p"))))),
                        Text(". Each zero-times-log-zero endpoint term is defined as zero, and all logarithms are natural.")),
                    Paragraph(Text("For any real r in [-1,1], specialize qubit_holevo_contraction with its parameters x=0, z=1 and t=abs(r). The disk hypothesis holds at (0,1), and abs(r) lies in [0,1]. Unfolding QubitNormalFormState.qubitHolevo and QubitNormalFormState.qubit_state_entropy identifies the scaled Holevo entropy with ln(2) minus h((1+abs(r))/2), while the unscaled value is ln(2). The identity sqrt(r squared)=abs(r) and binary-entropy symmetry h(p)=h(1-p) remove the absolute value; h(1/2)=ln(2) and h(1)=0 evaluate the endpoints. The contraction therefore gives "),
                        Math(Seq(Call("ln", D(2)), Minus, Call("h", Seq(Frac, Grp(D(1), Plus, F.Id("r")), Grp(D(2)))), Le, Sp, F.Id("r"), Caret, Grp(D(2)), Thin, Call("ln", D(2)))),
                        Text(". This includes both signs and the endpoint coordinates.")),
                    Paragraph(Text("Now let x, y and z be real numbers in the closed unit ball, so their squared coordinates sum to at most one. Each coordinate is in [-1,1]. Applying the preceding bound to each coordinate and adding yields "),
                        Math(Seq(Call("h", Seq(Frac, Grp(D(1), Plus, F.Id("x")), Grp(D(2)))), Plus,
                            Call("h", Seq(Frac, Grp(D(1), Plus, F.Id("y")), Grp(D(2)))), Plus,
                            Call("h", Seq(Frac, Grp(D(1), Plus, F.Id("z")), Grp(D(2)))),
                            Ge, Sp, Open, D(3), Minus, Open, F.Id("x"), Caret, Grp(D(2)), Plus, F.Id("y"), Caret, Grp(D(2)), Plus, F.Id("z"), Caret, Grp(D(2)), Close, Close, Thin, Call("ln", D(2)),
                            Ge, Sp, D(2), Thin, Call("ln", D(2)))),
                        Text(". The last step uses nonnegativity of ln(2), so the conclusion covers the entire closed ball, including its interior and boundary.")),
                    Paragraph(Text("At (1,0,0) the three entropy values are 0, ln(2) and ln(2). Changing the nonzero coordinate to -1 or permuting coordinates gives the same total. Thus the universal lower bound 2 ln(2) is sharp. These examples do not classify all equality cases. This is an application of the existing contraction theorem; a physical Born-probability interpretation, a stronger uncertainty relation and a literature novelty claim are outside this derivation."))),
                DescribeRole.Theorem))));

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
