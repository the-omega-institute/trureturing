using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinA235301CertificateDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Certificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The initial signed residual certificate for A235301.",
        H("Initial residual certificate"),
        Blocks(Describe.Lean(DescribeId.Create("initial-certificate"),
            DeclarationHandle.Create(Owner + ".initial_certificate"), H("Initial residual identities"),
            StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The kernel checks three identities on signed histories. The third residual "
                + "is the normalized concatenation of the preceding two with coefficients minus three and "
                + "minus two. Grouping the first two histories by mask gives the empty list in each case."))),
            DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("initial-path"),
                DeclarationHandle.Create(Owner + ".initialPath"), H("Initial transfer histories"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("initialPath"), Colon, Sp, Call("Fin", D(1, 0)),
                    Sp, To, Sp, Call("Hist", F.Id("State"))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The entries are the stored histories for heights one through ten."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("initial-path-eq"),
                DeclarationHandle.Create(Owner + ".initial_path_eq"), H("Correctness of the initial histories"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("i"), Colon, Sp, Call("Fin", D(1, 0)),
                    Comma, Sp, Eqn(Call("path", Seq(Call("val", F.Id("i")), Plus, D(1))),
                        Call("initialPath", F.Id("i")))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each entry uses the corresponding checked row-transfer identity. "
                    + "The square recurrence uses these histories to compute the initial literal counts."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula Residual(byte i) => Call("residualHist", D(i));
        var combined = Seq(Call("scaleHist", Seq(Minus, D(3)), Residual(1)), Sp, Plus, Plus, Sp,
            Call("scaleHist", Seq(Minus, D(2)), Residual(0)));
        var empty = Seq(OpenBracket, CloseBracket);
        return Seq(Eqn(Residual(2), Call("normalize", F.Id("stateKey"), combined)), Sp, Land, Sp,
            Eqn(Call("groupMask", Residual(0)), empty), Sp, Land, Sp,
            Eqn(Call("groupMask", Residual(1)), empty));
    }

    private static Formula Eqn(Formula left, Formula right) => Seq(left, Sp, F.Eq, Sp, right);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
}
