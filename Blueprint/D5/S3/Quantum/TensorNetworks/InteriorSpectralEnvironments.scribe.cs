using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class InteriorSpectralEnvironmentsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/InteriorSpectralEnvironments";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native positive-environment transport", H("Native positive-environment transport"), Blocks(
            Item("native_environment_transport", "Exact gauge and positive-scalar iterate transport",
                "For every admissible c,e, arbitrary complex rows l and r and natural N,p,q, leftTarget of l S equals normSq(u) to minus p times S dagger dualTransfer(A) iterated p on l dagger l times S. The native right target is exactly G squared times the outside congruence normSq(u) to N-q times S inverse transfer(A) iterated q on r r dagger times S inverse dagger, times G squared dagger. The scalar is written normSq(u)^N times inverse(normSq(u)^q), so N=0 is included. This follows from native_extraction and finite transfer iteration. G is never moved into the iterate.", DescribeRole.Theorem),
            Item("certificate_positive_targets", "Both actual native target matrices are positive definite",
                "For p,q at least one, real canonical x with positive sigma and P(p,q)(x) nonzero, and every e squared=D(coreCoordinates x), BOTH actual native leftTarget at p and rightTarget at q for the full nativeRight at N=(p+2)+q of sqrt(sigma)(1,eta) are PosDef. Jden supplies c2 nonzero; Wnorm supplies the exact nonzero determinant of the two canonical right seed columns. The original positive_iterates is exposed in place with its body unchanged and reused. Exact gauge transport, strictly positive normSq(u) scalars, invertible S and its inverse, and invertible G squared preserve PosDef. The right congruence remains outside transfer iteration.", DescribeRole.Theorem),
            Paragraph(Text("This environment bridge is consumed by the lengthwise canonical exclusion theorem. It proves no observed-image density or full C9 conclusion. The original C8 canonical source attribution remains Ma-Zhang, CC BY 4.0.")))));
    private static DocumentBlock Item(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("interiorspectralenvironments-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
