using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.NativeReader;

internal sealed class PropagationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full native propagation at every physical call time.", H("Full native propagation at every physical call time"),
        Blocks(Describe.Lean(
            DescribeId.Create("native-reader-propagation"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeReader/Propagation.full_operator_bound"),
            H("Full native propagation at every physical call time"), StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The matrices act on every one of the 610 extended coordinates with the Euclidean operator norm. Their exact source/tail block identity transports the existing weighted-path Hermitian projection laws to the full carrier. The phase is retained. Existing spectral-block multiplication gives unitarity. The pinned complex phase bound gives an error at most twice the angle change per changed factor. Chronological product induction counts the four occurrences of address eleven and two of address thirteen. Thus every internal time s in [0,1] in every one of the fifteen physical calls has operator error at most 12*abs(lambda-alpha). No input-state norm or projected subcarrier is substituted for this operator estimate. The proof uses standard algebra and norm bookkeeping and earns no additional content credit. Its live consumer is the auxiliary no-jump and propagation result in History. The native Bell probability law, report total variation witness and full source/archive history correspondence are additional obligations."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Statement() => Disp(Seq(Forall, Sp, F.Id("lambda"), Comma, Sp, Forall, Sp, F.Id("k"), Colon, Sp, Call("Fin", D(15)), Comma, Sp, Forall, Sp, F.Id("s"), Comma, Sp, Call("InUnitInterval", F.Id("s")), Sp, Implies, Sp, Call("OperatorNormDifference", Call("fullInternalOperator", F.Id("lambda"), F.Id("k"), F.Id("s")), Call("fullInternalOperator", F.Id("alpha"), F.Id("k"), F.Id("s"))), Sp, Leq, Sp, D(12), Sp, Times, Sp, Call("abs", Seq(F.Id("lambda"), Sp, Minus, Sp, F.Id("alpha")))));
}
