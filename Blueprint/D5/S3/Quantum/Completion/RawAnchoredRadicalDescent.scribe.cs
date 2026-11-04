using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class RawAnchoredRadicalDescentDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.";
    private static Formula M => F.Id("M");
    private static Formula U => F.Id("U");
    private static Formula C => F.Id("c");
    private static Formula Raw => Call("RawBalance", U, C);
    private static Formula Theorem => Call("rawAnchoredRadicalDescent", U, C);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The raw C133-V balance yields the anchored free comparison form, its two-sided radical quotient, and the exact marker transport identities.",
        H("Raw Anchored Radical Descent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("raw-anchored-radical-descent"),
                DeclarationHandle.Create(Gid + "raw_anchored_radical_descent"),
                H("Anchored radical descent and marker transport"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, M, Colon, Sp, F.Id("Type"), Comma, Sp,
                    OpenBracket, Call("MulOneClass", M), CloseBracket, Comma, Sp,
                    U, Sp, To, Sp, M, Comma, Sp,
                    C, Sp, To, Sp, M, Sp, To, Sp, M, Sp, To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Raw, Sp, Rightarrow, Sp, Theorem))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The construction uses the actual finite-support free real carrier e_a = δ_a − δ_1 and the bilinear kernel (c(a,1)+c(1,b)−c(a,b))/2. The two-sided radical is quotiented before marker transport. RawBalance supplies the exact marker invariance, period-three row and column readouts, anchored-form invariance, radical stability, beta(Ua) transport, R^3 beta identity, and the unit defect identities. No associativity, commutativity, cancellation, positivity or Hilbert representation is assumed."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "This is a finite Section 2 dependency unit for C133 Continuation V. The ordered Fourier constraints, defect pairing isotropy and full Hilbert representation remain open until separately derived from the constructed quotient.")))));
}
