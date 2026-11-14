using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.NativeReader;

internal sealed class GlobalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full native matrix propagation retains every source column.",
        H("Full native matrix propagation retains every source column"),
        Blocks(Describe.Lean(
            DescribeId.Create("fullDuring-factor"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeReader/Global.fullDuring_factor"),
            H("Full native matrix propagation retains every source column"), StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("fullProjection uses the literal native weighted coefficient at physical center 10+j, equality away from that center and the actual neighboring bits, including fixed b15=1 for the last address. fullPulse keeps its global phase. Both matrices act on the complete Extended carrier. The proof derives zero off-source coefficients and identifies each same-source row with the original full legal-tail projection. Summation over fullCarrierEquiv then proves exact source/tail factorization of the actual matrix action.")), Paragraph(Text("For every complex source vector chi, every real lambda, every actual call k and internal real time s, fullDuring equals GlobalDuringVector. The latter denotes globalVector(chi,i mapped to during(i,lambda,k,s)), whose (q,z) coordinate is chi(q)*during(b9(q),lambda,k,s)(z). This identity retains all coordinates and phases, including zero-support source columns. It assumes no source-specific factorization certificate. full_reader_uniform_nonvanishing applies the proved uniform tail theorem: the same eta works for every chi and every q with chi(q) nonzero. This does not assert that an arbitrary chi is operationally preparable. The exact original-prefix preparation bridge and native Bell source probability law remain additional obligations; this module supplies neither of them."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Statement() => Disp(Seq(Forall, Sp, F.Id("chi"), Colon, Sp, Call("SourceVector"), Comma, Sp, Forall, Sp, F.Id("lambda"), Colon, Sp, F.Id("Real"), Comma, Sp, Forall, Sp, F.Id("k"), Colon, Sp, Call("Fin", D(15)), Comma, Sp, Forall, Sp, F.Id("s"), Colon, Sp, F.Id("Real"), Comma, Sp, Call("fullDuring", F.Id("chi"), F.Id("lambda"), F.Id("k"), F.Id("s")), Sp, Eq, Sp, Call("GlobalDuringVector", F.Id("chi"), F.Id("lambda"), F.Id("k"), F.Id("s"))));
}
