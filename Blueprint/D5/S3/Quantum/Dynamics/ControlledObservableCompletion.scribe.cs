using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class ControlledObservableCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite nonnegative Hamiltonian control words have a sharp observable completion.",
        H("Controlled Observable Completion"),
        Blocks(Describe.Lean(
            DescribeId.Create("controlled-observable-completion"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Dynamics/ControlledObservableCompletion."
                    + "controlled_observable_completion"),
            H("Controlled observations and minimal expectation coordinates"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For any finite Hermitian control family and any finite Hermitian readout "
                        + "family on complex matrices of size m, a legal word is a finite list "
                        + "of controls with nonnegative real durations. The empty word is legal. "
                        + "Each segment pulls a readout back by U(t)^* E U(t), where "
                        + "U(t) = exp(-itH). The identity enters as a normalization observable "
                        + "and is not an additional measured readout.")),
                Paragraph(Text(
                    "Starting with the real span of the identity and the readouts, adjoining "
                        + "all images under i[H_a,-] reaches an equal consecutive step by "
                        + "m^2 minus the initial real dimension. Every later step is equal. "
                        + "The final Hermitian space is the real span of the identity and all "
                        + "actual legal word readouts, and is the least space containing the "
                        + "initial observables and invariant under every control generator.")),
                Paragraph(Text(
                    "Two density matrices have equal terminal expectations for every legal "
                        + "word exactly when their difference annihilates this final space under "
                        + "the trace pairing. A real-linear summary sufficient on physical "
                        + "density states has restriction rank at least dim(W)-1 on trace-zero "
                        + "Hermitian directions. Real trace expectations against a centered "
                        + "orthonormal observable basis attain that rank and are themselves "
                        + "sufficient for every legal prediction. Natural-number "
                        + "subtraction gives zero for m=0, where there are no density states. "
                        + "The rank claim concerns linear expectation summaries."))),
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

    private static Formula TheoremFormula()
    {
        Formula m = F.Id("m"), k = F.Id("k"), w = F.Id("W");
        Formula w0 = Seq(w, Underscore, Grp(D(0)));
        Formula wk = Seq(w, Underscore, Grp(k));
        Formula wnext = Seq(w, Underscore, Grp(k, Sp, Plus, Sp, D(1)));
        Formula dim = Call("dim", w);
        Formula rho = Rho, sigma = F.Id("sigma"), observable = F.Id("O");
        Formula trace = Call("Tr", Seq(Open, rho, Sp, Minus, Sp, sigma, Close, observable));
        Formula summary = F.Id("S"), coords = F.Id("C"), word = F.Id("word");
        Formula b = F.Id("b"), i = F.Id("i"), a = F.Id("A");
        Formula oi = Seq(F.Id("O"), Underscore, Grp(i));
        Formula ci = Seq(F.Id("C"), Underscore, Grp(i));
        Formula sufficient = Call("SufficientPhysical", summary);
        Formula coordSufficient = Call("SufficientPhysical", coords);
        return Disp(Seq(
            Exists, Sp, k, Sp, Leq, Sp, m, Caret, Grp(D(2)), Sp, Minus, Sp,
            Call("dim", w0), Comma, Sp, wk, Sp, Eq, Sp, wnext, Sp, Eq, Sp, w,
            Comma, RowBreak, Grp(),
            Call("PredictEq", rho, sigma), Sp, Iff, Sp,
            Forall, Sp, observable, Sp, InMacro, Sp, w, Comma, Sp,
            trace, Sp, Eq, Sp, D(0), Comma, RowBreak, Grp(),
            sufficient, Sp, Colon, Eq, Sp,
            Forall, Sp, rho, Comma, Sp, sigma, Sp, InMacro, Sp, F.Id("Density"),
            Comma, Sp, Call("S", rho), Sp, Eq, Sp, Call("S", sigma),
            Sp, Rightarrow, Sp, Forall, Sp, word, Sp, InMacro, Sp,
            F.Id("LegalWords"), Comma, Sp, Forall, Sp, b, Comma, Sp,
            Call("Tr", Seq(rho, Sp, Call("wordReadout", word, b))), Sp, Eq, Sp,
            Call("Tr", Seq(sigma, Sp, Call("wordReadout", word, b))),
            Comma, RowBreak, Grp(),
            sufficient, Sp, Rightarrow, Sp,
            Call("rank", Call("S", F.Id("Herm0"))), Sp, Geq, Sp,
            dim, Sp, Minus, Sp, D(1), Comma, RowBreak, Grp(),
            Exists, Sp, F.Id("r"), Comma, Sp, coords, Comma, Sp, oi, Comma, Sp,
            coordSufficient, Sp, Land, Sp,
            Open,
            Forall, Sp, i, Sp, InMacro, Sp, Call("Fin", F.Id("r")), Comma, Sp,
            oi, Sp, InMacro, Sp, w, Close, Sp, Land, Sp,
            Open, Forall, Sp, a, Comma, Sp,
            Forall, Sp, i, Sp, InMacro, Sp, Call("Fin", F.Id("r")), Comma, Sp,
            ci, Open, a, Close, Sp, Eq, Sp,
            Call("ReTr", Seq(a, Sp, oi)), Close, Sp, Land, Sp,
            Call("rank", Call("C", F.Id("Herm0"))), Sp, Eq, Sp,
            F.Id("r"), Sp, Eq, Sp, dim, Sp, Minus, Sp, D(1), Dot));
    }
}
