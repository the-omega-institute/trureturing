using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;
internal sealed class CommonLowerHarmonicBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common positive lower matrix and a complex split", H("CommonLowerHarmonicBound"), Blocks(
            Describe.Lean(DescribeId.Create("common-split"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/CommonLowerHarmonicBound.common_lower_split_bound"),
                H("A common positive lower matrix and a complex split"), StatementSource.FromAuthor(Seq(Forall, Sp, Seq(F.Id("u")), Colon, Call("Level"), Comma, Esc, Seq(Forall, Sp, Seq(F.Id("d")), Colon, Call("Type", F.Id("u")), Comma, Esc, Seq(Grp(Seq(Call("Fintype", F.Id("d")), Land, Sp, Call("DecidableEq", F.Id("d")))), Implies, Sp, Seq(Forall, Sp, Seq(F.Id("P"), Comma, F.Id("Q"), Comma, F.Id("K")), Colon, Call("Matrix", F.Id("d"), F.Id("d"), Seq(Mathbb, Grp(F.Id("C")))), Comma, Esc, Seq(Grp(Seq(Call("PosSemidef", F.Id("K")), Land, Sp, Seq(F.Id("K"), Le, Sp, F.Id("P")), Land, Sp, Seq(F.Id("K"), Le, Sp, F.Id("Q")))), Implies, Sp, Seq(Forall, Sp, Seq(F.Id("W")), Colon, Call("Prod", Call("Matrix", F.Id("d"), F.Id("d"), Seq(Mathbb, Grp(F.Id("C")))), Call("Matrix", F.Id("d"), F.Id("d"), Seq(Mathbb, Grp(F.Id("C"))))), Comma, Esc, Seq(Grp(Seq(Seq(Seq(Open, Call("fst", F.Id("W")), Close), Plus, Seq(Open, Call("snd", F.Id("W")), Close)), Eq, D(1))), Implies, Sp, Seq(F.Id("K"), Le, Sp, Seq(Seq(Open, D(2), Close), Times, Sp, Seq(Open, Call("splitEnergy", F.Id("P"), F.Id("Q"), F.Id("W")), Close))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/codex2026productmargin")),
                Blocks(Paragraph(Text("For every split W1+W2=I, the common lower matrix K is bounded by twice the split energy. Both inputs can be singular. The residual for the equal K inputs is (W1-W2) adjoint times K times (W1-W2); monotonicity in each input gives the bound. The split matrices themselves can be arbitrary complex matrices. Applying this bound to the attained identity split of ParallelSumVariational.parallel_sum_minimum gives domination by twice the parallel sum for positive definite inputs. That application introduces no new theorem. The general split bound gives the closed-disk trace estimate and the pure-factor annihilation argument."))), DescribeRole.Theorem))));

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
