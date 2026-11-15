using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.NativeReader;

internal sealed class InvariantsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual entrance charge is not identically zero.",
        H("The actual entrance charge is not identically zero"),
        Blocks(Describe.Lean(
            DescribeId.Create("entranceCharge-at-zero"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeReader/Invariants.entranceCharge_at_zero"),
            H("The actual entrance charge is not identically zero"), StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For an actual two-point vector v and opposite center a, charge(a,v) is star(v) dot sourceQ*v minus sourceQ(a,a) times star(v) dot v. Both quadratic forms are conserved by the literal pairPulse. A zero current coordinate v(not-a) forces the charge to vanish. Consequently a nonzero charge excludes that zero at every internal real time. sourceQ idempotence is derived from the exact full projection restriction; its Hermitian property is checked on the same literal entries. The original block_mul and block_star declarations are consumed directly at their owner after reindexing the two-point matrix.")), Paragraph(Text("entranceCharge(i,a,k,lambda) evaluates this charge on the actual finite pulse entrance restricted to the legal edge. The theorem states nonzero charge at the mathematical reference lambda=0 for every sector, changed address and entrance index. reference_entrance and pair_ready give a nonzero scalar multiple of the ready basis vector; x>0 and x<1 give the nonzero diagonal difference. entranceCharge_analytic additionally proves real analyticity of this same expression, including complex conjugation as a real-linear operation. These are live inputs to the isolated-zero argument. The quadratic identities and analytic machinery are standard; no supplied invariant certificate, arbitrary input-state replacement, or external process law is used."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Statement() => Disp(Seq(Forall, Sp, F.Id("i"), Colon, Sp, F.Id("Bool"), Comma, Sp, Forall, Sp, F.Id("a"), Colon, Sp, F.Id("Bool"), Comma, Sp, Forall, Sp, F.Id("k"), Colon, Sp, F.Id("Nat"), Comma, Sp, Call("entranceCharge", F.Id("i"), F.Id("a"), F.Id("k"), D(0)), Sp, Neq, Sp, D(0)));
}
